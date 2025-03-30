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
