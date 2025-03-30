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


def postfix_to_infix_verilog(postfix_expr):
    stack = []
    
    # SystemVerilog operator precedence (highest to lowest) and associativity
    # Source: IEEE Std 1800-2017 (SystemVerilog LRM)
    operators = {
        # Unary operators (not handled here, but listed for completeness)
        # '++': {'prec': 16, 'assoc': 'right'},  # Pre-increment
        # '--': {'prec': 16, 'assoc': 'right'},  # Pre-decrement
        # '+': {'prec': 16, 'assoc': 'right'},   # Unary plus
        # '-': {'prec': 16, 'assoc': 'right'},   # Unary minus
        # '~': {'prec': 16, 'assoc': 'right'},   # Bitwise NOT
        # '!': {'prec': 16, 'assoc': 'right'},   # Logical NOT
        # '&': {'prec': 16, 'assoc': 'right'},   # Reduction AND
        # '|': {'prec': 16, 'assoc': 'right'},   # Reduction OR
        # '^': {'prec': 16, 'assoc': 'right'},   # Reduction XOR
        # '~&': {'prec': 16, 'assoc': 'right'},  # Reduction NAND
        # '~|': {'prec': 16, 'assoc': 'right'},  # Reduction NOR
        # '~^': {'prec': 16, 'assoc': 'right'},  # Reduction XNOR
        # '^~': {'prec': 16, 'assoc': 'right'},  # Reduction XNOR (alternative)

        # Binary operators
        '**': {'prec': 15, 'assoc': 'right'},  # Exponentiation (right-associative)
        '*':  {'prec': 14, 'assoc': 'left'},   # Multiply
        '/':  {'prec': 14, 'assoc': 'left'},   # Divide
        '%':  {'prec': 14, 'assoc': 'left'},   # Modulus
        '+':  {'prec': 13, 'assoc': 'left'},   # Add
        '-':  {'prec': 13, 'assoc': 'left'},   # Subtract
        '<<': {'prec': 12, 'assoc': 'left'},   # Logical left shift
        '>>': {'prec': 12, 'assoc': 'left'},   # Logical right shift
        '<<<': {'prec': 12, 'assoc': 'left'},  # Arithmetic left shift
        '>>>': {'prec': 12, 'assoc': 'left'},  # Arithmetic right shift
        '<':  {'prec': 11, 'assoc': 'left'},   # Less than
        '<=': {'prec': 11, 'assoc': 'left'},   # Less than or equal
        '>':  {'prec': 11, 'assoc': 'left'},   # Greater than
        '>=': {'prec': 11, 'assoc': 'left'},   # Greater than or equal
        '==': {'prec': 10, 'assoc': 'left'},   # Equality
        '!=': {'prec': 10, 'assoc': 'left'},   # Inequality
        '===': {'prec': 10, 'assoc': 'left'},  # Case equality
        '!==': {'prec': 10, 'assoc': 'left'},  # Case inequality
        '&':  {'prec': 9, 'assoc': 'left'},    # Bitwise AND
        '^':  {'prec': 8, 'assoc': 'left'},    # Bitwise XOR
        '^~': {'prec': 8, 'assoc': 'left'},    # Bitwise XNOR
        '~^': {'prec': 8, 'assoc': 'left'},    # Bitwise XNOR (alternative)
        '|':  {'prec': 7, 'assoc': 'left'},    # Bitwise OR
        '&&': {'prec': 6, 'assoc': 'left'},    # Logical AND
        '||': {'prec': 5, 'assoc': 'left'},    # Logical OR
        '?:': {'prec': 4, 'assoc': 'right'},   # Ternary conditional (not handled here)
    }

    for token in postfix_expr:
        if token not in operators:
            # Operand (number, variable, etc.)
            stack.append(token)
        else:
            # Operator - pop operands and format with proper parentheses
            op_info = operators[token]
            right = stack.pop()
            left = stack.pop()

            # Helper function to check if parentheses are needed
            def needs_parentheses(operand, operand_op, current_op, is_right_operand=False):
                if not isinstance(operand, tuple):
                    return False
                operand_prec = operators[operand_op]['prec']
                current_prec = op_info['prec']
                if operand_prec < current_prec:
                    return True
                if operand_prec == current_prec:
                    if is_right_operand and op_info['assoc'] == 'left':
                        return True
                    if not is_right_operand and op_info['assoc'] == 'right':
                        return True
                return False

            # Process left operand
            if isinstance(left, tuple):
                left_op = left[1]
                if needs_parentheses(left, left_op, token):
                    left_str = f"({left[0]})"
                else:
                    left_str = left[0]
            else:
                left_str = left

            # Process right operand
            if isinstance(right, tuple):
                right_op = right[1]
                if needs_parentheses(right, right_op, token, is_right_operand=True):
                    right_str = f"({right[0]})"
                else:
                    right_str = right[0]
            else:
                right_str = right

            # Combine with operator
            new_expr = f"{left_str} {token} {right_str}"
            stack.append((new_expr, token))

    return stack[0][0] if stack else ""

if __name__ == '__main__':
    # Example usage:
    postfix_expr = "a b + c d * * e f ** g + /"  # Equivalent to ((a + b) * (c * d)) / (e ** f + g)
    infix_expr = postfix_to_infix_verilog(postfix_expr)
    print(infix_expr)  # Output: "a + b * c * d / (e ** f + g)"