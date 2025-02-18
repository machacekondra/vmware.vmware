from __future__ import absolute_import, division, print_function
__metaclass__ = type

import json

from ansible.module_utils import basic
from ansible.module_utils._text import to_bytes

from mock import patch


def set_module_args(**args):
    if '_ansible_remote_tmp' not in args:
        args['_ansible_remote_tmp'] = '/tmp'
    if '_ansible_keep_remote_files' not in args:
        args['_ansible_keep_remote_files'] = False

    args = json.dumps({'ANSIBLE_MODULE_ARGS': args})
    basic._ANSIBLE_ARGS = to_bytes(args)


class AnsibleExitJson(Exception):
    pass


class AnsibleFailJson(Exception):
    pass


def exit_json(*args, **kwargs):
    if 'changed' not in kwargs:
        kwargs['changed'] = False
    raise AnsibleExitJson(kwargs)


def fail_json(*args, **kwargs):
    kwargs['failed'] = True
    raise AnsibleFailJson(kwargs)


class ModuleTestCase:
    def setup_method(self):
        self.mock_module = patch.multiple(
            basic.AnsibleModule, exit_json=exit_json, fail_json=fail_json,
        )
        self.mock_module.start()

    def teardown_method(self):
        self.mock_module.stop()


def generate_name(test_case):
    return test_case['name']