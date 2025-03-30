def shunting_yard(tokens):
    """Convert infix tokens to postfix notation (RPN) using Shunting Yard algorithm."""
    PRECEDENCE = {
        '**': 15, '!': 14, '~': 14,  # Unary ops would need special handling
        '*': 12, '/': 12, '%': 12,
        '+': 11, '-': 11,
        '<<': 10, '>>': 10, '<<<': 10, '>>>': 10,
        '<': 9, '<=': 9, '>': 9, '>=': 9,
        '==': 8, '!=': 8, '===': 8, '!==': 8,
        '&': 7, '^': 6, '^~': 6, '~^': 6,
        '|': 5,
        '&&': 4,
        '||': 3,
        '?': 2,
        ':': 1
    }
    RIGHT_ASSOC = {'**'}
    
    output = []
    op_stack = []
    
    for token in tokens:
        if token in PRECEDENCE:
            # Handle operator precedence and associativity
            while (op_stack and op_stack[-1] != '(' and
                   (PRECEDENCE[op_stack[-1]] > PRECEDENCE[token] or
                    (PRECEDENCE[op_stack[-1]] == PRECEDENCE[token] and 
                     token not in RIGHT_ASSOC))):
                output.append(op_stack.pop())
            op_stack.append(token)
        elif token == '(':
            op_stack.append(token)
        elif token == ')':
            # Pop until matching '('
            while op_stack and op_stack[-1] != '(':
                output.append(op_stack.pop())
            if not op_stack:
                raise ValueError("Mismatched parentheses")
            op_stack.pop()  # Remove the '('
        else:
            # Numbers or variables go directly to output
            output.append(token)
    
    # Pop remaining operators
    while op_stack:
        op = op_stack.pop()
        if op == '(':
            raise ValueError("Mismatched parentheses")
        output.append(op)
    
    return output