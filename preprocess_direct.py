def impossible(square, position, distances):
    return position < distances[square] or position > len(distances) - distances[square]

def knights_tour_direct_encoding(n, type="decision"):

    board = Board(n)
    neighbors = board.valid_moves_dict
    if type == "decision":
        g = Glucose3()
    else:
        g = mc.Counter()

    # chessboard = [[(n*i)+j for i in range(n)] for j in range(n)]
    num_vars = n*n
    #variable_matrix[i][j] represents if square i is in jth position in the path
    variable_matrix = [[(num_vars*i)+j+1 for j in range(num_vars)] for i in range(num_vars)]
    
    # Find distance from starting square for each square on board using bfs
    distances = [-1 for i in range(num_vars)]
    distances[0] = 0
    curr_max = [0]
    while len(curr_max) > 0:
        next_max = []
        for square in curr_max:
            for neighbor in board.valid_moves_dict[square]:
                if distances[neighbor] == -1:
                    distances[neighbor] = distances[square] + 1
                    next_max.append(neighbor)
        curr_max = next_max

    #For each position in the path exactly one square is selected 
    for p in range(num_vars):
        possible_squares = []
        # loop through squares
        for s1 in range(num_vars):
            # at least one possible square must be in position j
            if not impossible(s1, p, distances):
                possible_squares.append(variable_matrix[s1][p])
                # at most one square can be in position j
                for s2 in range(s1+1, num_vars):
                    # only add clause if both s1 and s2 are possible
                    if not impossible(s2, p, distances):
                        g.add_clause([-variable_matrix[s1][p], -variable_matrix[s2][p]])
        g.add_clause(possible_squares)
    
    #For each square exactly one position in the path is selected
    for s in range(num_vars):
        possible_positions = []
        # loop through positions in path
        for p1 in range(num_vars):
            # at least one possible position must be occupied by square s
            if not impossible(s, p1, distances):
                possible_positions.append(variable_matrix[s][p1])
                # at most one position can be occupied by square s
                for p2 in range(p1+1, num_vars):
                    # only add clause if both p1 and p2 are possible
                    if not impossible(s, p2, distances):
                        g.add_clause([-variable_matrix[s][p1], -variable_matrix[s][p2]])
        g.add_clause(possible_positions)
        
    #Valid transitions
    for s in range(num_vars):
        for p in range(num_vars-1):
            # only need to look at squares that are possible in position p
            if not impossible(s, p, distances):
                const = [-variable_matrix[s][p]]
                for n in neighbors[s]:
                    if not impossible(n, p+1, distances):
                        const.append(variable_matrix[n][p+1])
                g.add_clause(const)

    g.add_clause([variable_matrix[0][0]])
    last = neighbors[0][0]
    last_pos = num_vars-1
    g.add_clause([variable_matrix[last][last_pos]])

    return g, variable_matrix
