def extract_between(tokens, start_token, end_token,inclusive = False):
    """
    Extract all tokens between `start_token` and `end_token` (inclusive/exclusive).
    
    Args:
        tokens (list): List of (token_type, token_value) tuples.
        start_token (str/tuple): Token that marks the start (e.g., '=' or ('OPERATOR', '=')).
        end_token (str/tuple): Token that marks the end (e.g., ';' or ('SEMICOLON', ';')).
    
    Returns:
        list: List of matches, where each match is a sublist of tokens between `start_token` and `end_token`.
    """
    matches = []
    inside_match = False
    current_match = []
    if inclusive:
        current_match.append(start_token)
    for token in tokens:
        # Check if the current token matches `start_token`
        if not inside_match:
            if (isinstance(start_token, str)) and (token[1] == start_token):
                inside_match = True
            elif (isinstance(start_token, tuple)) and ((token[0], token[1]) == start_token):
                inside_match = True
            continue
        
        # If inside a match, collect tokens until `end_token` is found
        if inside_match:
            # Check if the current token matches `end_token`
            if (isinstance(end_token, str) and (token[1] == end_token)) or \
                (isinstance(end_token, tuple) and ((token[0], token[1]) == end_token)):
                if inclusive:
                    current_match.append(end_token)
                matches.append(current_match)
                current_match = []
                inside_match = False
            else:
                current_match.append(token)
                
    return matches