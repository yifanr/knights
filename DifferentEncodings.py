from pysat.solvers import Glucose3
import numpy as np
from pysat.card import *
import networkx as nx
import pyapproxmc as mc
import time

class Board:
    def __init__(self, dim):
        self.dim = dim
        self.valid_moves_dict = self.get_valid_moves_dict()


    def is_valid_move(self, x, y):
        return 0 <= x < self.dim and 0 <= y < self.dim

    def square_to_coordinates(self, square):
        return divmod(square, self.dim)

    def coordinates_to_square(self, x, y):
        return x * self.dim + y

    def knight_moves(self, square):
        x, y = self.square_to_coordinates(square)
        possible_moves = [(x + 2, y + 1), (x + 2, y - 1), (x - 2, y + 1), (x - 2, y - 1), (x + 1, y + 2), (x + 1, y - 2), (x - 1, y + 2), (x - 1, y - 2)]
        return [self.coordinates_to_square(*move) for move in possible_moves if self.is_valid_move(*move)]

    def get_valid_moves_dict(self):
        valid_moves_dict = {}
        for i in range(self.dim**2):
            valid_moves_dict[i] = self.knight_moves(i)
        return valid_moves_dict

    def get_graph(self):
        graph = [[0]*self.dim**2 for i in range(self.dim**2)]
        for i in range(self.dim**2):
            for j in range(self.dim**2):
                if j in self.valid_moves_dict[i]:
                    graph[i][j] = 1
        return graph


def knights_tour_unary_encoding(n, start, type="decision", enc_type=0):

    if type == "decision":
        g = Glucose3()
    else:
        g = mc.Counter()
    board = Board(n)
    G = board.get_graph()
    num_nodes = n**2
    num_positions = n**2
    counter = 1
    
    H = []
    for i in range(num_nodes):
        H.append([])
        for j in range(num_nodes):
            if G[i][j] == 1:
                H[i].append(counter)
                counter+=1
            else:
                H[i].append(0)

    # Find distance from starting square for each square on board using bfs
    distances = [-1 for i in range(num_nodes)]
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
    
    U = []
    for i in range(num_positions):
        U.append([])
        for j in range(num_positions):
            if j < distances[i] or j > num_positions - distances[i]:
                U[i].append(0)
            else:
                U[i].append(counter)
                counter+=1
    
    vpool = IDPool(occupied=[[0, counter+1]])
    
    #Constraint 1
    for i in range(num_nodes):
        const_vars = []
        for j in range(num_nodes):
            if H[i][j] != 0 and i != j: 
                const_vars.append(H[i][j])
        #Add clause corresponding to sum(const_vars) = 1
        const_clauses = CardEnc.equals(lits=const_vars, vpool=vpool, bound=1, encoding=enc_type).clauses
        for c in const_clauses:
            g.add_clause(c)

    #Constraint 2
    for j in range(num_nodes):
        const_vars = []
        for i in range(num_nodes):
            if H[i][j] != 0 and i != j:
                const_vars.append(H[i][j])
        #Add clause corresponding to sum(const_vars) = 1
        const_clauses = CardEnc.equals(lits=const_vars, vpool=vpool, bound=1, encoding=enc_type).clauses
        for c in const_clauses:
            g.add_clause(c)
    
    #Constraint 6 sum_p(Uip) = 1
    for i in range(num_nodes):
        const_clauses = CardEnc.equals(lits=[U[i][p] for p in range(num_positions) if U[i][p] != 0], vpool=vpool, bound=1, encoding=enc_type).clauses
        for c in const_clauses:
            g.add_clause(c)
    
    all_nodes = [i for i in range(num_nodes)]
    all_nodes_minus_start = all_nodes.copy()
    all_nodes_minus_start.remove(start)

    g.add_clause([U[start][0]])

    #Constraint 3' and 4'
    for i in all_nodes_minus_start:
        if H[start][i] != 0:
            #Add clause corresponding to H[start][i] IMP U[i][1]
            g.add_clause([-H[start][i], U[i][1]])
        if H[i][start] != 0:
            #Add clause corresponding to H[i][start] IMP U[i][num_pos-1]
            g.add_clause([-H[i][start], U[i][num_positions-1]])
    
    #Constraint 5'
    for i in all_nodes_minus_start:
        for p in range(1, num_nodes-1):
            for j in all_nodes_minus_start:
                if H[i][j] != 0 and i != j and U[i][p] * U[j][p+1] > 0:
                    #Add clause corresponding to H[i][j] and U[i][p] IMP U[j][p+1]
                    g.add_clause([-H[i][j], -U[i][p], U[j][p+1]])
    
    return g, H


def decimal_to_binary(decimal_number):
    binary_representation = bin(decimal_number)
    return binary_representation[2:] 

def pad_binary(exp_len, binary_string):
    return "0"*(exp_len-len(binary_string))+binary_string

def get_add1_clauses(x_vars, y_vars):
    #Clauses corresponding to y_vars = x_vars + 1
    all_clauses = []
    all_clauses.append([x_vars[-1], y_vars[-1]])
    all_clauses.append([-x_vars[-1], -y_vars[-1]])
    all_clauses.append([-x_vars[-1], y_vars[-2], x_vars[-2]])
    all_clauses.append([-x_vars[-1], -y_vars[-2], -x_vars[-2]])
    all_clauses.append([x_vars[-1], y_vars[-2], -x_vars[-2]])
    all_clauses.append([x_vars[-1], -y_vars[-2], x_vars[-2]])

    for i in range(len(x_vars)-2):
        all_clauses.append([y_vars[i+1], -x_vars[i+1], y_vars[i], x_vars[i]])
        all_clauses.append([y_vars[i+1], -x_vars[i+1], -y_vars[i], -x_vars[i]])
        all_clauses.append([-y_vars[i+1], y_vars[i], -x_vars[i]])
        all_clauses.append([-y_vars[i+1], -y_vars[i], x_vars[i]])
        all_clauses.append([x_vars[i+1], y_vars[i], -x_vars[i]])
        all_clauses.append([x_vars[i+1], -y_vars[i], x_vars[i]])
    return all_clauses

def knights_tour_binary_adder_encoding(n, start, type="decision", enc_type=0):

    if type == "decision":
        g = Glucose3()
    else:
        g = mc.Counter()
    board = Board(n)
    G = board.get_graph()
    num_nodes = n**2
    counter = 1

    H = []
    for i in range(num_nodes):
        H.append([])
        for j in range(num_nodes):
            if G[i][j] == 1:
                H[i].append(counter)
                counter+=1
            else:
                H[i].append(0)

    #Constraint 1
    for i in range(num_nodes):
        const_vars = []
        for j in range(num_nodes):
            if H[i][j] != 0 and i != j: 
                const_vars.append(H[i][j])
        #Add clause corresponding to sum(const_vars) = 1
        const_clauses = CardEnc.equals(lits=const_vars, bound=1, encoding=enc_type).clauses
        for c in const_clauses:
            g.add_clause(c)

    #Constraint 2
    for j in range(num_nodes):
        const_vars = []
        for i in range(num_nodes):
            if H[i][j] != 0 and i != j:
                const_vars.append(H[i][j])
        #Add clause corresponding to sum(const_vars) = 1
        const_clauses = CardEnc.equals(lits=const_vars, bound=1, encoding=enc_type).clauses
        for c in const_clauses:
            g.add_clause(c)


    #log encoding of the position variables
    num_positions = n**2
    pos_vars = []
    num_vars_log_encoding = int(np.ceil(np.log2(num_positions)))
    for pos in range(num_positions):
        pos_vars.append([])
        if pos == start:
            for i in range(num_vars_log_encoding):
                pos_vars[pos].append(0)
        else:
            for i in range(int(num_vars_log_encoding)):
                pos_vars[pos].append(counter)
                counter += 1

    all_nodes = [i for i in range(num_nodes)]
    all_nodes_minus_start = all_nodes.copy()
    all_nodes_minus_start.remove(start)

    # for var in pos_vars[start]:
    #     g.add_clause([-var])

    #Constraint 3" and 4"
    for i in all_nodes_minus_start:
        if H[start][i] != 0:
            #Add clause corresponding to H[start][i] IMP P[i] = 1
            last_index = len(pos_vars[i]) - 1
            for ind in range(len(pos_vars[i])):
                if ind == last_index:
                    g.add_clause([-H[start][i], pos_vars[i][ind]])
                else:
                    g.add_clause([-H[start][i], -pos_vars[i][ind]])

        if H[i][start] != 0:
            #Add clause corresponding to H[i][start] IMP P[i] = num_positions-1
            binary = decimal_to_binary(num_positions-1)
            for l in range(len(pos_vars[i])):
                if binary[l] == "1":
                    g.add_clause([-H[i][start], pos_vars[i][l]])
                else:
                    g.add_clause([-H[i][start], -pos_vars[i][l]])

    #Constraint 5"
    for i in all_nodes_minus_start:
        for j in all_nodes_minus_start:
            if H[i][j] != 0 and i != j:
                #Add clause corresponding to H[i][j] IMP pos_vars[j] = pos_vars[i] + 1
                all_clauses = get_add1_clauses(pos_vars[i], pos_vars[j])
                for c in all_clauses:
                    c.append(-H[i][j])
                    g.add_clause(c)
    
    # #preprocessing
    graph_matrix = np.array(G)
    graph = nx.from_numpy_array(graph_matrix)
    shortest_path_to_start = nx.single_source_shortest_path_length(graph, start)
    for key in shortest_path_to_start.keys():
        if key != start:
            for t in range(0, shortest_path_to_start[key]):
                binary_t = pad_binary(num_vars_log_encoding, decimal_to_binary(t))
                clause_to_add = []
                for l in range(len(pos_vars[key])):
                    if binary_t[l] == "1":
                        clause_to_add.append(-pos_vars[key][l])
                    else:
                        clause_to_add.append(pos_vars[key][l])
                g.add_clause(clause_to_add)
            for t in range(num_positions-shortest_path_to_start[key]+1, num_positions):
                binary_t = pad_binary(num_vars_log_encoding, decimal_to_binary(t))
                clause_to_add = []
                for l in range(len(pos_vars[key])):
                    if binary_t[l] == "1":
                        clause_to_add.append(-pos_vars[key][l])
                    else:
                        clause_to_add.append(pos_vars[key][l])
                g.add_clause(clause_to_add)

    return g, H

def check_validity_of_solution_unary_binary(n, H, g):
    def last_nonzero_value(lst):
        # Iterate through the list in reverse order
        for value in reversed(lst):
            if value != 0:
                # Return the value of the last non-zero element
                return value

    num_nodes = n**2
    board = Board(n)

    last_h_var = last_nonzero_value(H[-1])

    H_sols = [i for i in g.get_model() if i >= 1 and i < last_h_var+1]

    New_H = [[0]*num_nodes for i in range(num_nodes)]

    for i in range(num_nodes):
        for j in range(num_nodes):
            if H[i][j] != 0:
                if H[i][j] not in H_sols:
                    New_H[i][j] = 0
                else:
                    New_H[i][j] = 1
    path_dict = {}
    for i in range(num_nodes):
        path_dict[i] = np.where(np.array(New_H)[i] == 1)[0]

    visited_nodes = [0]
    while len(visited_nodes) < num_nodes:
        if path_dict[visited_nodes[-1]][0] in board.valid_moves_dict[visited_nodes[-1]]:
            if path_dict[visited_nodes[-1]][0] not in visited_nodes:
                visited_nodes.append(path_dict[visited_nodes[-1]][0])
            else:
                return "ERROR"

    visited_nodes_sorted = sorted(visited_nodes)
    if len(visited_nodes) == num_nodes and visited_nodes_sorted == list(range(num_nodes)):
        return "CORRECT"
    else:
        return "ERROR"

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
    last = neighbors[0][0]
    last_pos = num_vars-1
    g.add_clause([variable_matrix[last][last_pos]])

    return g, variable_matrix

def check_validity_of_solution_direct(n, variables, g):
    node_to_position_dict = {}
    for i in range(n**2):
        for j in range(n**2):
            if variables[i][j] in g.get_model():
                if i not in node_to_position_dict.keys():
                    node_to_position_dict[i] = [j]
                else:
                    node_to_position_dict[i].append(j)

    #reverse the node_to_position_dict
    position_to_node_dict = {}
    for key in node_to_position_dict.keys():
        for val in node_to_position_dict[key]:
            position_to_node_dict[val] = key

    path =  []
    for i in range(n**2):
        path.append(position_to_node_dict[i])

    board = Board(n)
    G = board.get_graph()
    for i in range(n**2-1):
        if G[path[i]][path[i+1]] != 1:
            return "ERROR"

    if len(path) == n**2:
        return "CORRECT"
    else:
        return "ERROR"



n=8

print("====DIRECT ENCODING====")
g, variables = knights_tour_direct_encoding(n)
print(g.nof_vars(), g.nof_clauses())
start = time.time()
print("Solution is SAT: ", g.solve())
print("Solve time direct: " + str(time.time()-start))
print("Solution is valid: ", check_validity_of_solution_direct(n, variables, g))
print("\n")

print("====UNARY ENCODING====")
g, H = knights_tour_unary_encoding(n, 0, type="decision", enc_type=0)
print(g.nof_vars(), g.nof_clauses())
start = time.time()
print("Solution is SAT: ", g.solve())
print("Solve time unary: " + str(time.time()-start))
print("Solution is valid: ", check_validity_of_solution_unary_binary(n, H, g))
print("\n")

print("====BINARY ENCODING====")
g, H = knights_tour_binary_adder_encoding(n, 0, type="decision", enc_type=0)
print(g.nof_vars(), g.nof_clauses())
start = time.time()
print("Solution is SAT: ", g.solve())
print("Solve time binary: " + str(time.time()-start))
print("Solution is valid: ", check_validity_of_solution_unary_binary(n, H, g))
