def tokenize(expr):
    """Tokenize SystemVerilog expression while preserving existing groupings."""
    token_spec = [
        ('COMMENT', r'//.*?$|/\*.*?\*/'),
        ('PAREN', r'[()]'),
        ('Array', r'[\[\]]'),
        ('CONCAT', r'[{}]'),
        ('COMMA', r'''[,]'''),
        ('BIT_CAST', r''''[bhdBHD]'''),
        ('HEX_NUM', r'''(?<='[hH])[0-9A-F]+'''),
        ('BIN_NUM', r'''(?<='[bB])[0-1]+'''),
        ('DEC_NUM', r'''(?<='[dD])[0-9]+'''),
        ('LOGICAL_OPS',r'&&|\|\||!'),
        ('BITWISE_OPS', r'~&|~\||~^|[~&|^]'),
        ('OPERATOR', r'<<<=|>>>=|<<=|>>=|<=|>=|===|!==|==?|!=?|\+\+|--|\*\*|->|<->|[+*/%!<>:=%-]'),
        ('TERNARY',r'[?]'),
        ('NUMBER', r'\d+\'[bhdBHD]?\s*[0-9a-fA-F_xzXZ?]+|\d+\.\d+|\d+'),
        ('L_IDENT', r'[a-zA-Z_$][\w$]*(?=\s*=\s*)'),
        ('R_IDENT', r'[a-zA-Z_$][\w$]*'),
        ('SEMICOLON', r';+'),
        ('SKIP', r'\s+'),
        ('MISMATCH', r'.')
    ]
    tok_regex = '|'.join(f'(?P<{name}>{pattern})' for name, pattern in token_spec)
    tokens = []
    square_bracket_depth = 0  # Track array bracket nesting
    curly_bracket_depth = 0 # Track concatination and replication bracket nesting
    paren_depth = 0 # Track parentheses depth nesting
    ternary_depth = 0 # Ternary Depth
    colon_seeking_queue = []
    
    for mo in re.finditer(tok_regex, expr, re.MULTILINE):
        kind = mo.lastgroup
        value = mo.group()
        if kind == 'COMMENT' or kind == 'SKIP':
            continue
        elif kind == 'MISMATCH':
            raise ValueError(f'Unexpected character: {value}')
        
        # Update array context tracking
        if value == '[': 
            square_bracket_depth += 1
            colon_seeking_queue.append('[')
        elif value == ']': 
            square_bracket_depth -= 1
        elif value == '{':
            curly_bracket_depth += 1
        elif value == '}':
            curly_bracket_depth -= 1  
        elif value == '(':
            kind = kind + f"_{paren_depth}"
            paren_depth += 1
        elif value == ')':
            paren_depth -= 1
            kind = kind + f"_{paren_depth}"
        elif value == '?':
            ternary_depth += 1
            colon_seeking_queue.append('?')
            
        # Update based on more specific cases
        if value == ":":
            if colon_seeking_queue[-1] == '[':
                kind = "ARRAY_COLON"
                colon_seeking_queue.pop()
            elif colon_seeking_queue[-1] == '?':
                kind = "TERNARY_COLON"
                colon_seeking_queue.pop()
            else:
                kind = "COLON"     
        #TODO handling the concatination  
        if value == ",":
            kind = "CONCAT_COMMA" if curly_bracket_depth > 0 else 'COMMA'
            
        #TODO something for port
        
        #TODO something for parameters
            
        tokens.append((kind, value))
    return tokens


def body_grouping(body):
    token_pattern = [
        ('COMMENT', r'//.*?$|/\*.*?\*/'),
        ('PAREN', r'[()]'),
        ("2STATE_TYPE",r'bit|byte|shortint|longint|int'),
        ("4STATE_TYPE",r'logic|reg|integer|time'),
        ("NET_TYPE",r'wire|tri|wand|wor|triand|trior|supply0|supply1|'), 
        ('COMP_TYPE',r'struct|union|enum|packed|unpacked\b)'), # Composite Types
        ("TYPEDEF",r'typedef'),
        ("SIG_MOD",r"")
        ("GENERATE",r'generate'),
        ("GENVAR",r'genvar\s+[a-ZA-Z_][/w]+')  # combine the genvar and genvar name
        ("ENDGENERATE",r'endgenerate'),
        ("IF",r'if'),
        ('ELIF',r'else if'),
        ('ELSE'r'else'),
        ("PLI_FUNC",r'$[\w]+(.*?)'),
        ("DELAY",r"#[\w]+"),
        ('ASSIGN', r'assign\s+(\w)+'),
        ("ALWAYS_BLK",r'always_[cfl][afo][a-z]*|always(?!\w)'),
        ('SENS_LIST' r'@\s*\((.*?)\)'),
        ('BEGIN',r'begin\s+'),
        ('END'),r'end\s+',
        ("ENDCASE",r'endcase'),
        ('INSIDE',r'inside'),
        ("SEMICLON",r';'),
        ('STATEMENT'),
        ('SKIP', r'[\s\n]+'),
        ('MISMATCH', r'.')
    ]
    case_depth = 0
    case_cond = False
    case_active = FALSE
    block_depth = 0
    always_block_active = FALSE
    
    if 'begin':
        block_depth += 1
    elif 'end':
        block_depth -= 1
        
    # Start the always block active tag
    if kind == 'ALWAYS' or kind == 'ALWAYS_COMB' or kind == 'ALWAYS_FF' or kind == 'ALWAYS_LATCH':
        always_block_active = TRUE
    # end the always block tag
    elif kind == 'end' and block_depth == 0:
        always_block_active = FALSE
            
    if 'case':
        case_depth += 1
        case_active = True
    elif 'endcase':
        casse_active = FALSE
    elif case_active and kind == "PAREN":
        case_cond = TRUE
    elif case_cond and kind == "PAREN":
        case_cond = FALSE
        
    if case_depth > 1 and kind == "PAREN":
        value = 'PAREN_CASE'
    elif  and kind == "IDENT":
        value = 'CASE_COND'
