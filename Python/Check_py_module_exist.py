
import importlib
import os

def check_python_installation():
    module_name = 'errno'
    try:
        importlib.import_module(module_name)
        print(f"Python {module_name} is installed.")
    except ImportError:
        print(f"Python {module_name} is not installed.")
 
 
def check_builtin_python_modules():
    os.sys('python3 -c "help('modules')"')
# Call the function to check Python installation

check_python_installation()