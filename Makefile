units:
	ansible-test units --docker --python 3.12

integration:
	ansible-test integration -vvvv --no-temp-workdir vm_vm_drs_rule
