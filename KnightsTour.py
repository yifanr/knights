from pysat.solvers import Glucose3

def is_valid_move(x, y):
    return 0 <= x < 8 and 0 <= y < 8

def square_to_coordinates(square):
    return divmod(square, 8)

def coordinates_to_square(x, y):
    return x * 8 + y

def knight_moves(square):
    x, y = square_to_coordinates(square)
    possible_moves = [(x + 2, y + 1), (x + 2, y - 1), (x - 2, y + 1), (x - 2, y - 1), (x + 1, y + 2), (x + 1, y - 2), (x - 1, y + 2), (x - 1, y - 2)]
    return [coordinates_to_square(*move) for move in possible_moves if is_valid_move(*move)]

def get_valid_moves_dict():
    valid_moves_dict = {}
    for i in range(64):
        valid_moves_dict[i] = knight_moves(i)
    return valid_moves_dict

def knights_tour(n):
    # Initialize the PySAT solver
    neighbors = get_valid_moves_dict()
    g = Glucose3()

    # chessboard = [[(n*i)+j for i in range(n)] for j in range(n)]
    num_vars = n*n
    #variable_matrix[i][j] represents if square i is in jth position in the path
    variable_matrix = [[(num_vars*i)+j+1 for j in range(num_vars)] for i in range(num_vars)]
    
        
    #For each position in the path exactly one sqaure is selected 
    for j in range(num_vars):
        g.add_clause([variable_matrix[i][j] for i in range(num_vars)])
        for s in range(num_vars):
            for t in range(s+1, num_vars):
                g.add_clause([-variable_matrix[s][j], -variable_matrix[t][j]])
    
    #For each square exactly one position in the path is selected
    for i in range(num_vars):
        g.add_clause([variable_matrix[i][j] for j in range(num_vars)])
        for s in range(num_vars):
            for t in range(s+1, num_vars):
                g.add_clause([-variable_matrix[i][s], -variable_matrix[i][t]])

    #Valid transitions
    for i in range(num_vars):
        for j in range(num_vars-1):
            const = [-variable_matrix[i][j]]
            for k in neighbors[i]:
                const.append(variable_matrix[k][j+1])
            g.add_clause(const)

    g.add_clause([variable_matrix[0][0]])
    g.add_clause([variable_matrix[10][63]])

    return g

g = knights_tour(8)
print(g.solve())
# print(g.get_model())
x = g.get_model()
print(sum([i>0 for i in x]))

positive_vars = []
for i in x:
    if i>0:
        positive_vars.append(i)
print(positive_vars)

def var_to_square(var):
    return divmod(var, 64)

for var in positive_vars:
    square = var_to_square(var-1)
    print(square_to_coordinates(square[0]), square[1])