#!/bin/usr/env python3

def global_dictionary():
    global include_filelist = []
    global define_macro = {}
    global signal_value = {}
    

def get_preprocessor_directives(verilog_code):
    
    global include_filelist
    global define_macro
    
    # Pre-process: Normalize line continuations (\) for multi-line defines
    normalized_code = re.sub(r'\\\s*\n', ' ', verilog_code)  # Join lines ending with backslash
    
    
    preprocessor_directives = [
        ("MACRO_DEF",r'''`(define|undef|ifdef|ifndef|else|elsif|endif)'''),
        ("INCLUDE_FILE", r'(`include)'),
        ("TIME_CONTROL", r'`(timescale|delay_mode_[/w]+)'),
        ("SIM_CONTROL", r'`(resetall|celldefine|endcelldefine|unconnected_drive|nounconnected_drive)'),
        ("ASSERT_COV", r'`(default_nettype|line|pragma)'),
        ("ADV_DIRECTIVES",r'`(begin_keywords|end_keywords|protect|endprotect|FILE|LINE)')
    ]
    preprocessor_directives_pattern = r'''(\b`[a-zA-Z_$][/w]*\s+)''' 

    all_preprocessor = re.findall(preprocessor_directives_pattern, normalized_code, re.VERBOSE | re.DOTALL)

    define_pattern = r'''
        (`define\s+)                    # Macro directive
        (\w+)                           # Capture macro name (group 1)
        (?:                             # Optional value part:
            \s+                         # Whitespace before value
            (                           # Capture group 2 for value:
                (?:                     # Non-capturing group:
                    (?!\s*(?:`\w+|;|/\*|//|\n|$))  # Negative lookahead for terminators
                    .       # Match any character
                )*                      # Repeat until terminator
            )
        )?                              # Value is optional
        (?=\s*(?:`\w+|;|/\*|//|\n|$))  # Positive lookahead for terminator
    '''
    include_pattern = r'`include\s+"([^"]+)"'
    
    timescale_pattern = r'`timescale'
    defines = re.findall(define_pattern,normalized_code,re.VERBOSE | re.DOTALL)
    cleaned_code = re.sub(define_pattern,'',normalized_code,0,re.VERBOSE | re.DOTALL)

    includes = re.findall(include_pattern, normalized_code,re.VERBOSE | re.DOTALL)
    
    # append each of the include file into the include filelist
    for include in includes:
        include_filelist.append(include)
        
    cleaned_code = re.sub(include_pattern,'',cleaned_code,0,re.VERBOSE | re.DOTALL)
    cleaned_code = re.sub(r'''\r''','',cleaned_code,0,re.VERBOSE | re.DOTALL)
    
    
def split_sv_file(file_path):
    """
    Splits a SystemVerilog file into logical segments using ';' as a delimiter,
    while respecting procedural blocks (always, initial, task, function).
    
    Args:
        file_path (str): Path to the SystemVerilog file.
    
    Returns:
        list: List of split code segments with preserved block structure.
    """
    with open(file_path, 'r') as f:
        content = f.read()

    # Remove single-line and multi-line comments to avoid false splits
    content = re.sub(r'//.*?\n', '\n', content)  # Single-line
    content = re.sub(r'/\*.*?\*/', '', content, flags=re.DOTALL|re.MULTILINE)  # Multi-line

    # Split on semicolons, but ignore those inside procedural blocks
    segments = [] # store all the various segments in a list
    current_segment = [] # collate the lines in a segment 
    in_block = False
    pending_block = False 
    has_begin = False
    block_depth = 0 
    generate_block = False
    generate_depth = 0

    for line in content.split('\n'):
        line = line.strip()
        if not line: # if it is an empty line 
            continue


        preprocessing_block = re.match(r'\b`(ifdef|ifndef|else|elsif|endif)\b',line)
        
        if preprocessing_block:
            
        # Check for procedural block starts (always, initial, task, function)
        procedural_block = re.match(r'\b(always|always_ff|always_comb|always_ff|initial|task|function)\b', line)
        generate_block = re.match(r'\b(generate|endgenerate)\b',line)
        
        # determine when a generate block begins
        if re.match(r'\bgenerate\b',line):
            generate_depth += 1
        # generate block end 
        if re.match(r'\bendgenerate\b',line):
            generate_depth -= 1
            if generate_depth == 0:
                generate_block = False
        
        # Detect 'begin' and 'end' keywords and count the begin and end statements
        if re.match(r'\bbegin\b',line):
            has_begin = True
            block_depth += 1
        if re.match(r'\bend\b',line):
            block_depth -= 1
            if block_depth == 0:
                has_begin = False
            
        # if a procedural or generate sv keyword is found 
        if procedural_block or generate_block:
            if has_begin: # if there is a begin statement 
                in_block = True # we know it will be a block 
            else: # Otherwise, we wait to see the subsequent line
                pending_block = True 
            current_segment.append(line) # append the line to the current_segment
        continue
                
        if pending_block and (has_begin or ';' in line): # if decision is pending, and there is either 'begin' keyword or a ;
            if has_begin: # if there is a begin keyword
                in_block = True # we can be certain we are in a procedural block
            current_segment.append(line) # append the line
            pending_block = False # we dont need this. We now need to look for an 'end' statement
            if not in_block: # Single-line block (no need begin/end)
                if not generate_block: # if this procedural block is not in a generate block
                    segments.append(' '.join(current_segment)) # append it as a segment
                    current_segment = [] # clear the segment
                else: # if it is in a generate
                    current_segment.append(line) # collate it as a segment 
                in_block = False # this procedural block has ended
            continue
                
        if(in_block): # if we are in a procedural block
            if procedural_block == True: # if another procedural block is called, we know this is not valid 
                #TODO better error handling
                print('Error: Procedural statement declared inside another procedural statement.') # call an error
            if block_depth == 0: # if the block depth is 0, we know this procedural block has ended
                in_block = False # we know this is the end of the current procedural block
                if not generate_block: # if it is not in a generate block 
                    segments.append(' '.join(current_segment)) # append it as a segment
                    current_segment = [] # clear current_segment for the subsequent runs
                else: # else if it in a generate block
                    current_segment.append(line) # collate as a "generate" segment 
            else: # else the block has not ended as block depth > 0
                current_segment.append(line) # continue adding lines to the current segment 
            continue
    
        # Case 4: Outside blocks → split on semicolons
        parts = [p.strip() for p in line.split(';') if p.strip()]
        for part in parts:
            segments.append(part)
                
    # Add remaining segments
    if current_segment:
        segments.append(' '.join(current_segment))

    return [s for s in segments if s]  

# Example usage
if __name__ == "__main__":
    sv_file = "example.sv"
    split_code = split_sv_file(sv_file)
    for i, segment in enumerate(split_code, 1):
        print(f"Segment {i}: {segment}") 
