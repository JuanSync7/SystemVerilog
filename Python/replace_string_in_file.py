#!/bin/usr/env python3
import re

def replace_string_in_file(file_path, pattern, replacement):
    """
    Searches for a string literal that matches a pattern in a file and replaces it with another string.

    :param file_path: Path to the file.
    :param pattern: The regex pattern to search for.
    :param replacement: The string to replace the matched pattern with.
    """
    try:
        # Open the file and read its contents
        with open(file_path, 'r') as file:
            file_contents = file.read()

        # Use regex to search and replace the pattern
        updated_contents = re.sub(pattern, replacement, file_contents)

        # Write the updated contents back to the file
        with open(file_path, 'w') as file:
            file.write(updated_contents)

        print(f"Replaced '{pattern}' with '{replacement}' in {file_path}")

    except FileNotFoundError:
        print(f"Error: The file {file_path} does not exist.")
    except Exception as e:
        print(f"An error occurred: {e}")
        

def read_file(file_path,method): 
    with open(file_path,'r') as f:
        return (
            f.read() if method == r'read' else  # return the entire file as a string
            f.readline() if method == r'readline' else # return a single line
            f.readlines() if method == r'readlines' else # return a list of all the lines
            None
        )
    
if __name__ == '__main__':
    
    filename = "a.txt"
    file_contents_as_string = read_file(filename,'read')
    file_contents_as_lines = read_file(filename,"readlines")
    files_contents_read_per_line = [read_file(filename,"readline") for i in filename]
    
        
