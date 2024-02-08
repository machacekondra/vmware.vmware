# -*- coding: utf-8 -*-

# Copyright: (c) 2015, Joseph Callen <jcallen () csc.com>
# Copyright: (c) 2018, Ansible Project
# Copyright: (c) 2018, James E. King III (@jeking3) <jking@apache.org>
# GNU General Public License v3.0+ (see LICENSES/GPL-3.0-or-later.txt or https://www.gnu.org/licenses/gpl-3.0.txt)
# SPDX-License-Identifier: GPL-3.0-or-later

from __future__ import absolute_import, division, print_function
__metaclass__ = type

import atexit
import ansible.module_utils.common._collections_compat as collections_compat
import json
import os
import socket
import ssl
import hashlib
import time
import traceback
from ansible.module_utils.compat.version import StrictVersion
from random import randint


REQUESTS_IMP_ERR = None
try:
    # requests is required for exception handling of the ConnectionError
    import requests
    HAS_REQUESTS = True
except ImportError:
    REQUESTS_IMP_ERR = traceback.format_exc()
    HAS_REQUESTS = False

PYVMOMI_IMP_ERR = None
try:
    from pyVim import connect
    from pyVmomi import vim, vmodl, VmomiSupport
    HAS_PYVMOMI = True
    HAS_PYVMOMIJSON = hasattr(VmomiSupport, 'VmomiJSONEncoder')
except ImportError:
    PYVMOMI_IMP_ERR = traceback.format_exc()
    HAS_PYVMOMI = False
    HAS_PYVMOMIJSON = False

from ansible.module_utils.six import iteritems, raise_from
from ansible.module_utils.basic import env_fallback, missing_required_lib
from ansible.module_utils.six.moves.urllib.parse import unquote


class TaskError(Exception):
    def __init__(self, *args, **kwargs):
        super(TaskError, self).__init__(*args, **kwargs)


class ApiAccessError(Exception):
    def __init__(self, *args, **kwargs):
        super(ApiAccessError, self).__init__(*args, **kwargs)


def check_answer_question_status(vm):
    """Check whether locked a virtual machine.

    Args:
        vm: Virtual machine management object

    Returns: bool
    """
    if hasattr(vm, "runtime") and vm.runtime.question:
        return True

    return False


def make_answer_response(vm, answers):
    """Make the response contents to answer against locked a virtual machine.

    Args:
        vm: Virtual machine management object
        answers: Answer contents

    Returns: Dict with answer id and number
    Raises: TaskError on failure
    """
    response_list = {}
    for message in vm.runtime.question.message:
        response_list[message.id] = {}
        for choice in vm.runtime.question.choice.choiceInfo:
            response_list[message.id].update({
                choice.label: choice.key
            })

    responses = []
    try:
        for answer in answers:
            responses.append({
                "id": vm.runtime.question.id,
                "response_num": response_list[answer["question"]][answer["response"]]
            })
    except Exception:
        raise TaskError("not found %s or %s or both in the response list" % (answer["question"], answer["response"]))

    return responses


def answer_question(vm, responses):
    """Answer against the question for unlocking a virtual machine.

    Args:
        vm: Virtual machine management object
        responses: Answer contents to unlock a virtual machine
    """
    for response in responses:
        try:
            vm.AnswerVM(response["id"], response["response_num"])
        except Exception as e:
            raise TaskError("answer failed: %s" % to_text(e))


def wait_for_task(task, max_backoff=64, timeout=3600, vm=None, answers=None):
    """Wait for given task using exponential back-off algorithm.

    Args:
        task: VMware task object
        max_backoff: Maximum amount of sleep time in seconds
        timeout: Timeout for the given task in seconds

    Returns: Tuple with True and result for successful task
    Raises: TaskError on failure
    """
    failure_counter = 0
    start_time = time.time()

    while True:
        if check_answer_question_status(vm):
            if answers:
                responses = make_answer_response(vm, answers)
                answer_question(vm, responses)
            else:
                raise TaskError("%s" % to_text(vm.runtime.question.text))
        if time.time() - start_time >= timeout:
            raise TaskError("Timeout")
        if task.info.state == vim.TaskInfo.State.success:
            return True, task.info.result
        if task.info.state == vim.TaskInfo.State.error:
            error_msg = task.info.error
            host_thumbprint = None
            try:
                error_msg = error_msg.msg
                if hasattr(task.info.error, 'thumbprint'):
                    host_thumbprint = task.info.error.thumbprint
            except AttributeError:
                pass
            finally:
                raise_from(TaskError(error_msg, host_thumbprint), task.info.error)
        if task.info.state in [vim.TaskInfo.State.running, vim.TaskInfo.State.queued]:
            sleep_time = min(2 ** failure_counter + randint(1, 1000) / 1000, max_backoff)
            time.sleep(sleep_time)
            failure_counter += 1


def find_object_by_name(content, name, obj_type, folder=None, recurse=True):
    if not isinstance(obj_type, list):
        obj_type = [obj_type]

    name = name.strip()

    objects = get_all_objs(content, obj_type, folder=folder, recurse=recurse)
    for obj in objects:
        try:
            if unquote(obj.name) == name:
                return obj
        except vmodl.fault.ManagedObjectNotFound:
            pass

    return None


def find_cluster_by_name(content, cluster_name, datacenter=None):
    if datacenter and hasattr(datacenter, 'hostFolder'):
        folder = datacenter.hostFolder
    else:
        folder = content.rootFolder

    return find_object_by_name(content, cluster_name, [vim.ClusterComputeResource], folder=folder)


def find_vm_by_id(content, vm_id, vm_id_type="vm_name", datacenter=None,
                  cluster=None, folder=None, match_first=False):
    """ UUID is unique to a VM, every other id returns the first match. """
    si = content.searchIndex
    vm = None

    if vm_id_type == 'dns_name':
        vm = si.FindByDnsName(datacenter=datacenter, dnsName=vm_id, vmSearch=True)
    elif vm_id_type == 'uuid':
        # Search By BIOS UUID rather than instance UUID
        vm = si.FindByUuid(datacenter=datacenter, instanceUuid=False, uuid=vm_id, vmSearch=True)
    elif vm_id_type == 'instance_uuid':
        vm = si.FindByUuid(datacenter=datacenter, instanceUuid=True, uuid=vm_id, vmSearch=True)
    elif vm_id_type == 'ip':
        vm = si.FindByIp(datacenter=datacenter, ip=vm_id, vmSearch=True)
    elif vm_id_type == 'vm_name':
        folder = None
        if cluster:
            folder = cluster
        elif datacenter:
            folder = datacenter.hostFolder
        vm = find_vm_by_name(content, vm_id, folder)
    elif vm_id_type == 'inventory_path':
        searchpath = folder
        # get all objects for this path
        f_obj = si.FindByInventoryPath(searchpath)
        if f_obj:
            if isinstance(f_obj, vim.Datacenter):
                f_obj = f_obj.vmFolder
            for c_obj in f_obj.childEntity:
                if not isinstance(c_obj, vim.VirtualMachine):
                    continue
                if c_obj.name == vm_id:
                    vm = c_obj
                    if match_first:
                        break
    return vm


def get_all_objs(content, vimtype, folder=None, recurse=True):
    if not folder:
        folder = content.rootFolder

    obj = {}
    container = content.viewManager.CreateContainerView(folder, vimtype, recurse)
    for managed_object_ref in container.view:
        try:
            obj.update({managed_object_ref: managed_object_ref.name})
        except vmodl.fault.ManagedObjectNotFound:
            pass
    return obj


def find_vm_by_name(content, vm_name, folder=None, recurse=True):
    return find_object_by_name(content, vm_name, [vim.VirtualMachine], folder=folder, recurse=recurse)


def vmware_argument_spec():
    return dict(
        hostname=dict(type='str',
                      aliases=['vcenter_hostname'],
                      required=False,
                      fallback=(env_fallback, ['VMWARE_HOST']),
                      ),
        username=dict(type='str',
                      aliases=['vcenter_username', 'user', 'admin'],
                      required=False,
                      fallback=(env_fallback, ['VMWARE_USER'])),
        password=dict(type='str',
                      aliases=['vcenter_password', 'pass', 'pwd'],
                      required=False,
                      no_log=True,
                      fallback=(env_fallback, ['VMWARE_PASSWORD'])),
        port=dict(type='int',
                  default=443,
                  fallback=(env_fallback, ['VMWARE_PORT'])),
        validate_certs=dict(type='bool',
                            aliases=['vcenter_validate_certs'],
                            required=False,
                            default=True,
                            fallback=(env_fallback, ['VMWARE_VALIDATE_CERTS'])
                            ),
        proxy_host=dict(type='str',
                        required=False,
                        default=None,
                        fallback=(env_fallback, ['VMWARE_PROXY_HOST'])),
        proxy_port=dict(type='int',
                        required=False,
                        default=None,
                        fallback=(env_fallback, ['VMWARE_PROXY_PORT'])),
    )


def connect_to_api(module, disconnect_atexit=True, return_si=False, hostname=None, username=None, password=None, port=None, validate_certs=None,
                   httpProxyHost=None, httpProxyPort=None):
    if module:
        if not hostname:
            hostname = module.params['hostname']
        if not username:
            username = module.params['username']
        if not password:
            password = module.params['password']
        if not httpProxyHost:
            httpProxyHost = module.params.get('proxy_host')
        if not httpProxyPort:
            httpProxyPort = module.params.get('proxy_port')
        if not port:
            port = module.params.get('port', 443)
        if not validate_certs:
            validate_certs = module.params['validate_certs']

    def _raise_or_fail(msg):
        if module is not None:
            module.fail_json(msg=msg)
        raise ApiAccessError(msg)

    if not hostname:
        _raise_or_fail(msg="Hostname parameter is missing."
                       " Please specify this parameter in task or"
                       " export environment variable like 'export VMWARE_HOST=ESXI_HOSTNAME'")

    if not username:
        _raise_or_fail(msg="Username parameter is missing."
                       " Please specify this parameter in task or"
                       " export environment variable like 'export VMWARE_USER=ESXI_USERNAME'")

    if not password:
        _raise_or_fail(msg="Password parameter is missing."
                       " Please specify this parameter in task or"
                       " export environment variable like 'export VMWARE_PASSWORD=ESXI_PASSWORD'")

    if validate_certs and not hasattr(ssl, 'SSLContext'):
        _raise_or_fail(msg='pyVim does not support changing verification mode with python < 2.7.9. Either update '
                           'python or use validate_certs=false.')
    elif validate_certs:
        ssl_context = ssl.SSLContext(ssl.PROTOCOL_SSLv23)
        ssl_context.verify_mode = ssl.CERT_REQUIRED
        ssl_context.check_hostname = True
        ssl_context.load_default_certs()
    elif hasattr(ssl, 'SSLContext'):
        ssl_context = ssl.SSLContext(ssl.PROTOCOL_SSLv23)
        ssl_context.verify_mode = ssl.CERT_NONE
        ssl_context.check_hostname = False
    else:  # Python < 2.7.9 or RHEL/Centos < 7.4
        ssl_context = None

    service_instance = None

    connect_args = dict(
        host=hostname,
        port=port,
    )
    if ssl_context:
        connect_args.update(sslContext=ssl_context)

    msg_suffix = ''
    try:
        if httpProxyHost:
            msg_suffix = " [proxy: %s:%d]" % (httpProxyHost, httpProxyPort)
            connect_args.update(httpProxyHost=httpProxyHost, httpProxyPort=httpProxyPort)
            smart_stub = connect.SmartStubAdapter(**connect_args)
            session_stub = connect.VimSessionOrientedStub(smart_stub, connect.VimSessionOrientedStub.makeUserLoginMethod(username, password))
            service_instance = vim.ServiceInstance('ServiceInstance', session_stub)
        else:
            connect_args.update(user=username, pwd=password)
            service_instance = connect.SmartConnect(**connect_args)
    except vim.fault.InvalidLogin as invalid_login:
        msg = "Unable to log on to vCenter or ESXi API at %s:%s " % (hostname, port)
        _raise_or_fail(msg="%s as %s: %s" % (msg, username, invalid_login.msg) + msg_suffix)
    except vim.fault.NoPermission as no_permission:
        _raise_or_fail(msg="User %s does not have required permission"
                           " to log on to vCenter or ESXi API at %s:%s : %s" % (username, hostname, port, no_permission.msg))
    except (requests.ConnectionError, ssl.SSLError) as generic_req_exc:
        _raise_or_fail(msg="Unable to connect to vCenter or ESXi API at %s on TCP/%s: %s" % (hostname, port, generic_req_exc))
    except vmodl.fault.InvalidRequest as invalid_request:
        # Request is malformed
        msg = "Failed to get a response from server %s:%s " % (hostname, port)
        _raise_or_fail(msg="%s as request is malformed: %s" % (msg, invalid_request.msg) + msg_suffix)
    except Exception as generic_exc:
        msg = "Unknown error while connecting to vCenter or ESXi API at %s:%s" % (hostname, port) + msg_suffix
        _raise_or_fail(msg="%s : %s" % (msg, generic_exc))

    if service_instance is None:
        msg = "Unknown error while connecting to vCenter or ESXi API at %s:%s" % (hostname, port)
        _raise_or_fail(msg=msg + msg_suffix)

    # Disabling atexit should be used in special cases only.
    # Such as IP change of the ESXi host which removes the connection anyway.
    # Also removal significantly speeds up the return of the module
    if disconnect_atexit:
        atexit.register(connect.Disconnect, service_instance)
    if return_si:
        return service_instance, service_instance.RetrieveContent()
    return service_instance.RetrieveContent()


class PyVmomi(object):
    def __init__(self, module):
        """
        Constructor
        """
        if not HAS_REQUESTS:
            module.fail_json(msg=missing_required_lib('requests'),
                             exception=REQUESTS_IMP_ERR)

        if not HAS_PYVMOMI:
            module.fail_json(msg=missing_required_lib('PyVmomi'),
                             exception=PYVMOMI_IMP_ERR)

        self.module = module
        self.params = module.params
        self.current_vm_obj = None
        self.si, self.content = connect_to_api(self.module, return_si=True)
        self.custom_field_mgr = []
        if self.content.customFieldsManager:  # not an ESXi
            self.custom_field_mgr = self.content.customFieldsManager.field

    # Cluster related functions
    def find_cluster_by_name(self, cluster_name, datacenter_name=None):
        """
        Find Cluster by name in given datacenter
        Args:
            cluster_name: Name of cluster name to find
            datacenter_name: (optional) Name of datacenter

        Returns: True if found

        """
        return find_cluster_by_name(self.content, cluster_name, datacenter=datacenter_name)
