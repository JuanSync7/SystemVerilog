#!/bin/usr/env python3

import importlib
import os
import argparse

def parser():
    parser = argparse.ArgumentParser(description="Check if module exist",
        usage="./Check_py_module_exist.py --name <module_name> or --default_module", add_help=False
    )
    parser.add_argument('-n','--name',description="Module Name",help="Enter Module name",required=False,default=None)
    parser.add_argument('-dm','--default_module',help='Check Built-In Modules',description="Check Built-In Modules",action='store_true',required=False,default=None)
    
    return parser.parse_args()

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

if __name__ == "__main__":
    arg = parser()
    if not arg.name == None:
        check_python_installation(arg.module)
    elif not arg.default_module == None:
        check_builtin_python_modules()