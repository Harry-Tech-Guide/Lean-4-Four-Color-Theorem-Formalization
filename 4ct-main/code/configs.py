# Implementing configurations

# from IPython.display import display
import re
import itertools
# import graphviz
import ctypes
# graphviz.set_default_engine('sfdp') # for nice drawing of planar graphs


# import libcons C library and declare relevant types
# TODO: improve, need to declare argument and return types for all the functions I'm calling
libcons=ctypes.CDLL('./libcons.so')
libcons.compute_max_consistent_subset.restype = ctypes.c_char_p
libcons.compute_extendable_edge_colorings.argtypes = (ctypes.c_int32, ctypes.c_int32, ctypes.c_int32, ctypes.POINTER(ctypes.c_int32))
libcons.compute_extendable_edge_colorings.restype = ctypes.c_long
libcons.copy_computed_extendable_edge_colorings.argtypes = (ctypes.c_char_p, ctypes.c_long)



# import libnewreduce C library
# TODO: improve, need to declare argument and return types for all the functions I'm calling
libnewreduce=ctypes.CDLL('./libnewreduce.so')
libcons.compute_max_consistent_subset.restype = ctypes.c_int


class Configuration:
    def __init__(self, code):
        codelines = code.split('\n')

        # save the code in case it's needed to pass to the newreduce library check_config() function
        self.code = code
        
        # line 0: some useful parameters
        line0params = [int(s) for s in re.split('\s+',codelines[0].lstrip(' '))]
        self.num_vertices = line0params[0]
        self.ring_size = line0params[1]
        self.CKcount = line0params[2]
        self.CKprimecount = line0params[3]
        
        # line 1: ignoring, I think it's something related to contracts
        # TODO: check this
        
        # the configuration matrix: lines indexed 2 through self.num_vertices+1
        self.matrix = []
        self.degree_seq = []
        for j, codeline in enumerate(codelines[2:self.num_vertices+2]):
            lineparams = [int(s) for s in re.split('\s+',codeline.lstrip(' '))]
            assert lineparams[0]==j+1, f"Invalid configuration: configuration matrix line should be numbered, code=\n----- begin code-----\n{code}\n----- end code-----"
            self.degree_seq.append(lineparams[1])
            self.matrix.append(lineparams[2:])
            
        # the next lines: ignoring.
        # TODO: figure out what these lines are about and whether I need to do anything with them
        
        assert self.test_validity(), f"Invalid configuration: failed validity test, code=\n----- begin code-----\n{code}\n----- end code-----"
        
        self.computed_edge_adjacencies = None
        self.computed_extendable_edge_coloring_strings = None
        
        # compute the graph adjacency matrix - this will be useful later for various calculations
        self.adjacency_matrix = []
        for i in range(self.num_vertices):
            vertex_adjacencies = [0 for _ in range(self.num_vertices)]
            for j in range(self.degree_seq[i]):
                vertex_adjacencies[self.matrix[i][j]-1] = 1
            self.adjacency_matrix.append(vertex_adjacencies)
        

        
    def test_validity(self):
        # condition (1): checking that the value of self.ring_size is valid
        if self.ring_size > self.num_vertices or self.ring_size < 2:
            return False
        
        # condition (2): checking that the vertex degrees are valid
        for i in range(self.ring_size):
            if self.degree_seq[i] < 3 or self.degree_seq[i] >= self.num_vertices:
                return False
        for i in range(self.ring_size, self.num_vertices):
            if self.degree_seq[i] < 5 or self.degree_seq[i] >= self.num_vertices:
                return False

        # condition (3): checking that the vertex indices in the configuration matrix are valid indices
        for i in range(self.num_vertices):
            for j in range(self.degree_seq[i]):
                if self.matrix[i][j] < 1 or self.matrix[i][j] > self.num_vertices:
                    return False
        
        # condition (4): checking the first and last indices of the conf. matrix row associated with vertices in the ring
        for i in range(self.ring_size):
            if (i<self.ring_size-1 and self.matrix[i][0] != i+2) or (i==self.ring_size-1 and self.matrix[i][0] != 1):
                return False
            if (i>0 and self.matrix[i][self.degree_seq[i]-1] != i) or (i==0 and self.matrix[i][self.degree_seq[i]-1] != self.ring_size):
                return False
        
        # condition (5): checking that the degrees add up to the correct value
        if sum(self.degree_seq) != 6*self.num_vertices - 6 - 2*self.ring_size:
            return False
        
        # condition (6):
        for i in range(self.ring_size,self.num_vertices):
            specialjs = [j for j in range(self.degree_seq[i]-1) if self.matrix[i][j]>self.ring_size and self.matrix[i][j+1]<=self.ring_size]
            if len(specialjs)>2:
                return False
            elif len(specialjs)==2:
                j1, j2 = specialjs[0]+2, specialjs[1]+2
                if j1==self.degree_seq[i]:
                    j1 = 0
                if j2==self.degree_seq[i]:
                    j2 = 0
                if self.matrix[i][j1]<=self.ring_size or self.matrix[i][j2]<=self.ring_size:
                    return False
        
        # condition (7):
        for i in range(self.num_vertices):
            # TODO: add this
            pass

        return True
        
    def __str__(self):
        mystring = f"Configuration with {self.num_vertices} vertices and ring-size {self.ring_size}:\n|C(K)|={self.CKcount}, |C'(K)|={self.CKprimecount}"
        for j in range(self.num_vertices):
            mystring += f"\nVertex {j+1}: deg={self.degree_seq[j]}, list={self.matrix[j]}"
        return mystring

    # compile a list of edges in the configuration
    def edges(self):
        myedges = []
        for i in range(self.ring_size,self.num_vertices):
            for j in range(self.degree_seq[i]):
                if i+1<self.matrix[i][j] and self.matrix[i][j]>self.ring_size:
                    myedges.append((i+1,self.matrix[i][j]))
        return myedges

    # compile a list of edges in the free completion of the configuration
    def free_completion_edges(self):
        myedges = []
        for i in range(self.num_vertices):
            for j in range(self.degree_seq[i]):
                if i+1<self.matrix[i][j]:
                    myedges.append((i+1,self.matrix[i][j]))
        return myedges

    # a variant of the function to compile the list of edges in the free completion, in a way
    # that obeys the requirements of the algorithm described in Section 2 in the note
    # "Reducibility in the four-colour theorem" by Robertson, Sanders, Seymour and Thomas
    def free_completion_edges_section2_order(self):
        myedges = []
        
        # first add the edges going around the ring
        myedges.append((1,self.ring_size))
        for i in range(self.ring_size-1):
            myedges.append((i+1,i+2))
        
        # then add the remaining edges
        for i in range(self.num_vertices):
            for j in range(self.degree_seq[i]):
                if i+1<self.matrix[i][j] and (i+1,self.matrix[i][j]) not in myedges:
                    myedges.append((i+1,self.matrix[i][j]))
        
        # finally, make sure that the two last edges on the list are on a common triangle
        # we'll do this by scanning the list of edges that are not on the outer ring other than the last edge
        # until we find an edge that is on a common triangle with the last edge
        # once we find such an edge, move it to the next to last position
        num_edges = len(myedges)
        for i in range(self.ring_size, num_edges-2):
            if ((myedges[i][0]==myedges[num_edges-1][0] and self.adjacency_matrix[myedges[i][1]-1][myedges[num_edges-1][1]-1]==1) or
                (myedges[i][0]==myedges[num_edges-1][1] and self.adjacency_matrix[myedges[i][1]-1][myedges[num_edges-1][0]-1]==1) or
                (myedges[i][1]==myedges[num_edges-1][0] and self.adjacency_matrix[myedges[i][0]-1][myedges[num_edges-1][1]-1]==1) or
                (myedges[i][1]==myedges[num_edges-1][1] and self.adjacency_matrix[myedges[i][0]-1][myedges[num_edges-1][0]-1]==1)):
                # edge i and edge num_edges-1 are on a common triangle
                edge_to_move = myedges[i]
                myedges.pop(i)
                myedges.insert(num_edges-2, edge_to_move)
        
        return myedges
    
    def draw(self):
        myedges=self.edges()
        symbols="ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
        G=graphviz.Graph()
        for i in range(self.ring_size,self.num_vertices):
            if self.degree_seq[i]==5:
                G.node(symbols[i], "", style='filled', color='black', shape='circle')
            elif self.degree_seq[i]==6:
                G.node(symbols[i], "", style='invisible', color='black', shape='point')
            elif self.degree_seq[i]==7:
                G.node(symbols[i], "", style='solid', color='black', shape='circle')
            elif self.degree_seq[i]==8:
                G.node(symbols[i], "", style='solid', color='black', shape='square')
            elif self.degree_seq[i]==9:
                G.node(symbols[i], "", style='solid', color='black', shape='triangle')
            elif self.degree_seq[i]==10:
                G.node(symbols[i], "", style='solid', color='black', shape='pentagon')
            elif self.degree_seq[i]==11:
                G.node(symbols[i], "", style='solid', color='black', shape='star')
        G.edges([symbols[edge[0]-1]+symbols[edge[1]-1] for edge in myedges])
        display(G) # alternatively: G.view() to save the rendered graph image to file
        
    def draw_free_completion(self):
        myedges=self.free_completion_edges()
        symbols="ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
        G=graphviz.Graph()
        for i in range(self.num_vertices):
            G.node(symbols[i], "", style='filled', color='black', shape='circle')
        G.edges([symbols[edge[0]-1]+symbols[edge[1]-1] for edge in myedges])
        display(G) # alternatively: G.view() to save the rendered graph image to file
        
    # class method to read configurations from a file in the .conf format defined by Robertson, Sanders, Seymour and Thomas:
    # returns a list of Configuration objects read from the file
    @classmethod
    def read_configuration_file(cls, fname, report_success=False):
        counter = 0
        f = open(fname, "r")
        line=f.readline()
        current_conf_code = ""
        configs = []
        parsed_first_line = False
        while line:
            line=line.strip()
            if len(line)==0:
                if len(current_conf_code)>0:
                    parsed_first_line = False
                    configs.append(Configuration(current_conf_code))
                    current_conf_code = ""
            else:
                if not parsed_first_line:
                    conf_first_line = line
                    parsed_first_line = True
                    counter += 1
                    # print(f"parsing conf {conf_first_line}, counter={counter}")
                else:
                    current_conf_code += line + '\n'
            line=f.readline()
        if report_success:
            print(f"Read file with {len(configs)} configurations successfully")
        return configs
    
    def compute_edge_adjacencies(self):
        if self.computed_edge_adjacencies!=None:
            return # we already computed what we needed
        
        edges = self.free_completion_edges_section2_order()
        adjacencies = []
        for e in edges:
            adjacent_edges = []
            for i, f in enumerate(edges):
                if f!=e and (   (f[0]==e[0] and self.adjacency_matrix[f[1]-1][e[1]-1]==1)
                             or (f[0]==e[1] and self.adjacency_matrix[f[1]-1][e[0]-1]==1)
                             or (f[1]==e[0] and self.adjacency_matrix[f[0]-1][e[1]-1]==1)
                             or (f[1]==e[1] and self.adjacency_matrix[f[0]-1][e[0]-1]==1) ):
                    adjacent_edges.append(i)
            adjacencies.append(adjacent_edges)

        # store the results of the computation
        self.computed_fcedges = edges
        self.computed_edge_adjacencies = adjacencies
    



    def extendable_edge_coloring_strings_slow(self):
        self.compute_edge_adjacencies() # make sure we have the edge adjacencies available
        # if self.computed_extendable_edge_coloring_strings != None:
        #     return self.computed_extendable_edge_coloring_strings

        ring_edge_coloring_strings = {} # a dictionary to store string representations of the canonical extendable edge colorings
        n = self.num_vertices
        r = self.ring_size
        m = 3*n-3-r
        c = [None for _ in range(m)] # this is the array where we'll store the tricoloring. The values for the three colors are 1,2,4 (powers of 2 so we can use bitwise operations for a small efficiency gain)
        c[m-1], c[m-2], c[m-3] = 1,2,1 # we fix the colors of the last and next to last edge to 1 and 2
        forbidden = [0 for _ in range(m-2)] # called F in the paper, forbidden in RSST's reduce.c program
        j = m-2 # index of the edge we are currently trying to color (its color was initialized to 1 above)

        # after we've determined each edge-coloring we'll want to map the colors 1,2,4 to the more human-friendly colors r,g,b
        # the mapping from 1,2,4 to colors r,g,b comes in 6 possible permutations
        # the choice of permutation will be made so as to make the resulting coloring canonical
        # since we are only interested in counting canonical colorings
        powerof2_to_color_permutations = ["_rg_b", "_rb_g", "_gr_b", "_bg_r", "_gb_r", "_br_g"]

        # compute the forbidden colors for the initial edge with index m-2. This is a set of colors from 1,2,4 so can be conveniently stored as a bit mask
        for edge_index in self.computed_edge_adjacencies[j-1]:
            if edge_index>j-1:
                forbidden[j-1] |= c[edge_index]
        
        while True:
            # look for an available color for the current edge
            while (c[j-1] & forbidden[j-1]) and c[j-1] < 8:
                c[j-1] <<= 1
            if c[j-1]==8: # there is no available color, which means we have to backtrack up the tree
                j += 1
                if j>=m-1: # we came back to the root, so the depth first traversal of the tree is complete
                    self.computed_extendable_edge_coloring_strings = ring_edge_coloring_strings   # store the result for possible reuse later
                    return list(ring_edge_coloring_strings.keys())
                c[j-1] <<= 1 # cycle to the next color for this edge and go back to the beginning of the main while loop
            elif j>r+1: # we found a valid color but we're not done yet with this attempted coloring
                j -= 1 # move on to the next edge in need of coloring
                c[j-1] = 1 # after going down one level in the tree, always start from the color 1
                # make a list of forbidden colors for this edge based on the edges already colored
                forbidden[j-1] = 0
                for edge_index in self.computed_edge_adjacencies[j-1]:
                    if edge_index>j-1:
                        forbidden[j-1] |= c[edge_index]
            else: # (elif j==r+1:) # we found a valid color and it's the last edge that needed to be colored
                # TODO: the next line looks like an unused leftover from some earlier version, delete it if appropriate
                code = "" # we will encode the ring edge-coloring as a string of 'r','g','b' symbols in order to record it in a dictionary
                
                # compute the colors for the ring edges based on the internal edge colors
                for i in range(r):
                    # each ring edge shares a triangle with two already colored internal edges
                    c[i] = 7 - c[self.computed_edge_adjacencies[i][0]] - c[self.computed_edge_adjacencies[i][1]]
                
                # we need to permute the colors 1,2,4 to ensure the coloring we are recording is canonical,
                # here we identify the correct permutation to use:
                lastc = c[r-1]
                x = r-2
                while x>=0 and c[x]==c[r-1]:
                    x -= 1
                secondlastc = lastc if x==-1 else c[x]
                permutations_matrix = [[0,0,1],[2,2,5],[4,3,3]]
                inds = [None,0,1,None,2]
                p = permutations_matrix[inds[lastc]][inds[secondlastc]]

                # create and then record the edge-coloring string code
                string_code = ''.join([powerof2_to_color_permutations[p][c[i]] for i in range(r)])
                ring_edge_coloring_strings[string_code] = 1 # record the coloring in the strings dict

                c[j-1] <<= 1 # after recording this coloring, cycle to the next color for this edge




    def extendable_edge_coloring_strings(self):
        self.compute_edge_adjacencies() # make sure we have the edge adjacencies available
        # if self.computed_extendable_edge_coloring_strings != None:
        #     return self.computed_extendable_edge_coloring_strings
        
        num_edges = len(self.computed_edge_adjacencies)
        bytes_per_int = 4   # 32-bit int, to match the int32_t data type expected in the C-language function we are calling
        flattened_adjacencies = [0 for _ in range(4*num_edges)]
        for j,e in enumerate(self.computed_edge_adjacencies):
            flattened_adjacencies[4*j] = e[0]
            flattened_adjacencies[4*j+1] = e[1]
            if j>=self.ring_size:
                flattened_adjacencies[4*j+2] = e[2]
                flattened_adjacencies[4*j+3] = e[3]
        adjacencies_buffer = (ctypes.c_int32 * len(flattened_adjacencies))(*flattened_adjacencies)
        num_extendable_edge_colorings = libcons.compute_extendable_edge_colorings(self.num_vertices, self.ring_size, num_edges, adjacencies_buffer)
        num_bytes = num_extendable_edge_colorings * (self.ring_size+1) + 1
        edge_colorings_buffer = ('\0'*num_bytes).encode('utf-8')
        libcons.copy_computed_extendable_edge_colorings(edge_colorings_buffer, num_bytes)
        # return edge_colorings_buffer
        edge_colorings_string = edge_colorings_buffer[:-1].decode('utf-8')[:-1]
        # return edge_colorings_string
        return edge_colorings_string.split('\n')


    # def extendable_edge_coloring_codes(self):
    #     self.compute_edge_adjacencies()
    #     ring_edge_coloring_codes = {} # a dictionary to store code representations of the canonical extendable edge colorings, as defined in RSST's note
    #     n = self.num_vertices
    #     r = self.ring_size
    #     m = 3*n-3-r
    #     c = [None for _ in range(m)] # this is the array where we'll store the tricoloring. The values for the three colors are 1,2,4 (powers of 2 so we can use bitwise operations for a small efficiency gain)
    #     c[m-1], c[m-2], c[m-3] = 1,2,1 # we fix the colors of the last and next to last edge to 1 and 2
    #     forbidden = [0 for _ in range(m-2)] # called F in the paper, forbidden in reduce.c
    #     j = m-2 # index of the edge we are currently trying to color (its color was initialized to 1 above)

    #     powersof3 = [1, 3, 9, 27, 81, 243, 729, 2187, 6561, 19683, 59049, 177147, 531441, 1594323, 4782969, 14348907, 43046721, 129140163, 387420489, 1162261467, 3486784401]

    #     # compute the forbidden colors for the initial edge with index m-2. This is a set of colors from 1,2,4 so can be conveniently stored as a bit mask
    #     for edge_index in self.computed_edge_adjacencies[j-1]:
    #         if edge_index>j-1:
    #             forbidden[j-1] |= c[edge_index]


    #     powerof2_to_color_permutations = ["_rg_b", "_rb_g", "_gr_b", "_bg_r", "_gb_r", "_br_g"]
    #     colors_to_ints = { 'r':0, 'g':1, 'b':-1 }

        
    #     while True:
    #         # look for an available color for the current edge
    #         while (c[j-1] & forbidden[j-1]) and c[j-1] < 8:
    #             c[j-1] <<= 1
    #         if c[j-1]==8: # there is no available color, which means we have to backtrack up the tree
    #             j += 1
    #             if j>=m-1: # we came back to the root, so the depth first traversal of the tree is complete
    #                 return ring_edge_coloring_codes
    #             c[j-1] <<= 1 # cycle to the next color for this edge and go back to the beginning of the main while loop
    #         elif j>r+1: # we found a valid color but we're not done yet with this attempted coloring
    #             j -= 1 # move on to the next edge in need of coloring
    #             c[j-1] = 1 # after going down one level in the tree, always start from the color 1
    #             # make a list of forbidden colors for this edge based on the edges already colored
    #             forbidden[j-1] = 0
    #             for edge_index in self.computed_edge_adjacencies[j-1]:
    #                 if edge_index>j-1:
    #                     forbidden[j-1] |= c[edge_index]
    #         else: # (elif j==r+1:) # we found a valid color and it's the last edge that needed to be colored
    #             code = "" # we will encode the ring edge-coloring as a string of 'r','g','b' symbols in order to record it in a dictionary
                
    #             # compute the colors for the ring edges based on the internal edge colors
    #             for i in range(r):
    #                 # each ring edge shares a triangle with two already colored internal edges
    #                 c[i] = 7 - c[self.computed_edge_adjacencies[i][0]] - c[self.computed_edge_adjacencies[i][1]]

    #             # we need to permute the colors 1,2,4 to ensure the coloring we are recording is canonical,
    #             # here we identify the correct permutation to use:
    #             lastc = c[r-1]
    #             x = r-2
    #             while x>=0 and c[x]==c[r-1]:
    #                 x -= 1
    #             secondlastc = lastc if x==-1 else c[x]
    #             permutations_matrix = [[0,0,1],[2,2,5],[4,3,3]]
    #             inds = [None,0,1,None,2]
    #             p = permutations_matrix[inds[lastc]][inds[secondlastc]]

    #             # create and then record the edge-coloring string code
    #             string_code = ''.join([powerof2_to_color_permutations[p][c[i]] for i in range(r)])
    #             int_code = sum([colors_to_ints[string_code[u]] * 3**u for u in range(r)])
                
    #             # create and then record the edge-coloring integer code
    #             weights = [None, 0, 0, None, 0]
    #             for t in range(r):
    #                 weights[c[t]] += powersof3[t]
    #             min_weight = min(weights[1], weights[2], weights[4])
    #             max_weight = max(weights[1], weights[2], weights[4])
    #             int_code2 = (3**r-1)//2 - 2*min_weight - max_weight

    #             assert int_code==int_code2, f"error! {c} {int_code} {int_code2}"

    #             ring_edge_coloring_codes[int_code] = 1 # record the coloring in the int codes dict

    #             c[j-1] <<= 1 # after recording this coloring, cycle to the next color for this edge



    @classmethod
    def max_consistent_subset(cls, colorings):
        ring_size = len(colorings[0])
        colorings_as_bytes = ''.join(colorings).encode('utf-8')
        output_buffer = ('\0'*16384).encode('utf-8')    # TODO: there's probably a more correct/efficient way to allocate a memory buffer - improve
        libcons.compute_max_consistent_subset(ring_size, len(colorings), colorings_as_bytes, output_buffer)
        raw_output = output_buffer.decode('utf-8').rstrip('\0').split(',')
        output_dict = { "C" : list(map(int, raw_output[1::2])), "M" : list(map(int, raw_output[0:-1:2])), "R" : raw_output[-1] }
        return output_dict


    @classmethod
    def analyze_color_switching(cls, colorings):
        ring_size = len(colorings[0])
        number_of_edge_colorings = (3**(ring_size-1)+1)//2
        colorings_as_bytes = ''.join(colorings).encode('utf-8')
        output_buffer = ('\0'*(16384 + 4*number_of_edge_colorings)).encode('utf-8')    # TODO: there's probably a more correct/efficient way to allocate a memory buffer - improve
        libcons.analyze_color_switching_game(ring_size, len(colorings), colorings_as_bytes, output_buffer)
        split_output = output_buffer.decode('utf-8').split('***')
        raw_output = split_output[0].split(',')
        output_dict = { "C" : list(map(int, raw_output[1::2])), "M" : list(map(int, raw_output[0:-1:2])), "R" : raw_output[-1],
                       "thetas" : split_output[1], "moves" : list(map(int,split_output[2].rstrip('\0').split(','))) }
        return output_dict



    # this function is the interface to my C-language implementation RSST's reducibility-checking algorithm
    # from the library libcons (compiled from the file consistent.c)
    # the function calculates the maximal consistent subset of the complement of the set of canonical extendable colorings
    def compute_max_consistent_subset(self):
        # extendable_edge_colorings = self.extendable_edge_coloring_strings_slow()  // this uses the older Python code for extendable colorings
        extendable_edge_colorings = self.extendable_edge_coloring_strings()
        output_dict = Configuration.max_consistent_subset(extendable_edge_colorings)
        self.reducibility_check_output = output_dict


    # this function interfaces with a different version of my implementation of RSST's reducibility-checking 
    # algorithm from the library libcons (compiled from the file consistent.c), where the algorithm
    # is reformulated in terms of analyzing a two player game I call the color switching game
    # the output consists of the same information returned by the compute_max_consistent_subset function,
    # plus additional information about the winning strategy in the game
    def analyze_color_switching_for_extendable(self):
        extendable_edge_colorings = self.extendable_edge_coloring_strings()
        output_dict = Configuration.analyze_color_switching(extendable_edge_colorings)
        self.color_switching_game_output = output_dict



    # this function provides an interface to RSST's original C-language implementation of their reducibility-checking algorithm,
    # imported via the library libnewreduce (compiled from the file newreduce.c, my adaptation of RSST's original program reduce.c)
    def compute_max_consistent_subset_rsst(self):
        output_buffer = ('\0'*16384).encode('utf-8')    # TODO: there's probably a more correct/efficient way to allocate a memory buffer - improve
        configuration_code_as_cstring = self.code.encode('utf-8')
        libnewreduce.check_config(configuration_code_as_cstring, output_buffer)
        raw_output = output_buffer.decode('utf-8').rstrip('\0').split(',')
        if raw_output[-2]==raw_output[-4]:
            # remove elements in positions -2 and -3 to account for undesirable repetition
            # TODO: maybe better to fix this at the level of the C function and not return those numbers in the first place
            raw_output = raw_output[:-3] + [raw_output[-1]]
        output_dict = { "C" : list(map(int, raw_output[1::2])), "M" : list(map(int, raw_output[0:-1:2])), "R" : raw_output[-1] }
        self.reducibility_check_rsst_output = output_dict


    # this is a Python-language implementation of RSST's reducibility-checking algorithm
    # it was my first attempt at coding up the algorithm so is based on a very naive and non-optimized (and hence impractically slow)
    # version of the algorithm
    def compute_max_consistent_subset_very_slow(self):
        # some helper functions
        def all_edge_colorings(n):
            if n==0:
                return ['']
            return [c+a for c in all_edge_colorings(n-1) for a in ('r','g','b')]
        def is_canonical(edge_coloring):
            if edge_coloring[-1]!='r':
                return False
            j=len(edge_coloring)-2
            while edge_coloring[j]=='r' and j>=0:
                j -= 1
            if j>=0:
                return True if edge_coloring[j]=='g' else False
            return True
        def check_theta_fit(edge_coloring, theta, simatching):
            # check condition (i) in the definition
            matching_edges = [edge_index for edge_pair in simatching[1] for edge_index in edge_pair]
            edges_with_color_not_equal_theta = [j+1 for j in range(len(edge_coloring)) if edge_coloring[j]!=theta]
            if set(matching_edges)!=set(edges_with_color_not_equal_theta):
                return False # failed the test of condition (i)
            # if we got to this point, we passed condition (i)
            # check condition (ii) in the definition
            for k in range(len(simatching[0])):
                sign, edge_pair = simatching[0][k], simatching[1][k]
                if (edge_coloring[edge_pair[0]-1]==edge_coloring[edge_pair[1]-1] and sign==-1) or (edge_coloring[edge_pair[0]-1]!=edge_coloring[edge_pair[1]-1] and sign==1):
                    return False # failed the test of condition (ii)
            return True
        # computing the set of signed matchings
        def balanced_signed_matchings(n):
            # a helper function to generate all lists of +1 or -1 of length n
            def sign_lists(n): 
                if n==0:
                    return [[]]
                return [sl+[a] for sl in sign_lists(n-1) for a in (-1,1)]
            # a helper function to generate all noncrossing matchings between a given set of elements
            def noncrossing_matchings(elements, lowerindex=-1, upperindex=-1):
                if lowerindex < 0:
                    lowerindex = 0
                if upperindex < 0:
                    upperindex = len(elements)-1
                if upperindex<lowerindex+1:
                    return [[]]
                pairs = (upperindex-lowerindex+1)//2
                matchings = []
                for j in range(pairs):
                    smallmatchings1 = noncrossing_matchings(elements, lowerindex=lowerindex+1, upperindex=lowerindex+2*j)
                    smallmatchings2 = noncrossing_matchings(elements, lowerindex=lowerindex+2*j+2, upperindex=upperindex)
                    matchings.extend([[(elements[lowerindex],elements[lowerindex+2*j+1])]+m1+m2 for m1 in smallmatchings1 for m2 in smallmatchings2])
                return matchings
            def signs_are_balanced(signs, n):
                return ((n+signs.count(-1)) % 2 == 0)
            
            matchings = []
            elements = list(range(1,n+1))
            for j in range(0,n+1,2):
                subsets = itertools.combinations(elements,j)
                matchings.extend([(signs,m) for s in subsets for m in noncrossing_matchings(s) for signs in sign_lists(j//2)
                                    if signs_are_balanced(signs,n)])
            return matchings
        
        def edge_colorings_that_theta_fit(simatching, theta, n):
            dict = { 'r' : ('g','b'), 'g' : ('r','b'), 'b' : ('r','g') }
            otherthetas = dict[theta]
            num_pairs = len(simatching[0])
            template = [theta]*n
            possibilities = [[0,1]]*num_pairs
            colorings = []
            for poss in itertools.product(*possibilities):
                coloring = template.copy()
                for j in range(num_pairs):
                    if simatching[0][j]==1:
                        coloring[simatching[1][j][0]-1], coloring[simatching[1][j][1]-1] = otherthetas[poss[j]], otherthetas[poss[j]]
                    else:
                        coloring[simatching[1][j][0]-1], coloring[simatching[1][j][1]-1] = otherthetas[poss[j]], otherthetas[1-poss[j]]
                colorings.append(''.join(coloring))
            return colorings
        
        def edge_colorings_that_fit(simatching, n):
            return edge_colorings_that_theta_fit(simatching, 'r', n)+edge_colorings_that_theta_fit(simatching, 'g', n)+edge_colorings_that_theta_fit(simatching, 'b', n)


        alledge_colorings = all_edge_colorings(self.ring_size)
        extendable_edge_colorings = self.extendable_edge_coloring_strings()
        nonextendable_edge_colorings = [c for c in alledge_colorings if is_canonical(c) and c not in extendable_edge_colorings]
        simatchings = balanced_signed_matchings(self.ring_size)

        print(f"{len(extendable_edge_colorings)} ({self.CKcount}) extendable canonical edge-colorings, {len(nonextendable_edge_colorings)} nonextendable canonical")
        assert len(extendable_edge_colorings)==self.CKcount, "Calculated number of extendable canonical edge-colorings does not match the number read from file"

        # now start iteratively computing the sequence of sets \mathcal{C}_i, \mathcal{M}_i
        calCi = nonextendable_edge_colorings
        calMi = simatchings

        i = 0

        perms = [
            { 'r':'r', 'g':'g', 'b':'b' },
            { 'r':'g', 'g':'r', 'b':'b' },
            { 'r':'b', 'g':'g', 'b':'r' },
            { 'r':'r', 'g':'b', 'b':'g' },
            { 'r':'g', 'g':'b', 'b':'r' },
            { 'r':'b', 'g':'r', 'b':'g' }
        ]

        while True:
            print(f"step i={i}:  |C({i})|={len(calCi):<5} |M({i})|={len(calMi)}")
            i += 1

            # compute \mathcal{M}_{i+1}:
            # \mathcal{M}_{i+1} is the set of all signed matchings sm in \mathcal{M}_i for which for every coloring c,
            # if there exists a theta such that c theta-fits sm then c is in \mathcal{C}_i
            calMi_plus_one = [sm for sm in calMi if all([
                ((''.join([perms[0][col] for col in c]) in calCi)
                or (''.join([perms[1][col] for col in c]) in calCi)
                or (''.join([perms[2][col] for col in c]) in calCi)
                or (''.join([perms[3][col] for col in c]) in calCi)
                or (''.join([perms[4][col] for col in c]) in calCi)
                or (''.join([perms[5][col] for col in c]) in calCi))
                                                         for c in edge_colorings_that_fit(sm, self.ring_size)])]

            # compute \mathcal{C}_{i+1}:
            # \mathcal{C}_{i+1} is the set of all colorings c in \mathcal{C}_i for which for every theta there exists
            # a signed matching sm in \mathcal{M}_{i+1} such that c theta-fits sm
            calCi_plus_one = [c for c in calCi if any([check_theta_fit(c,'r',sm) for sm in calMi_plus_one]) \
                              and any([check_theta_fit(c,'g',sm) for sm in calMi_plus_one]) \
                              and any([check_theta_fit(c,'b',sm) for sm in calMi_plus_one])]
            
            if len(calCi) == len(calCi_plus_one):
                print(f"*** maximal consistent subset has {len(calCi)} ({self.CKprimecount}) colorings ***")
                assert len(calCi)==self.CKprimecount, "Calculated size of maximal consistent subset does not match the number read from file"
                return
            calMi = calMi_plus_one
            calCi = calCi_plus_one






    # *** some old code - commenting out for now ***
    # def classify_edge_colorings(self, fname):
    #     extendable_edge_colorings = list(self.extendable_edge_coloring_strings().keys())
    #     extendable_edge_colorings_as_bytes = ''.join(extendable_edge_colorings).encode('utf-8')
    #     fname_bytes = fname.encode('utf-8')
    #     libcons.edge_colorings_classifier(fname_bytes, self.ring_size, len(extendable_edge_colorings), extendable_edge_colorings_as_bytes)


