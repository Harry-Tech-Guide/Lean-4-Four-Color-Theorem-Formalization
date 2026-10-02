//
// C library implementing the algorithms from the paper "The four-colour theorem" and
// "Reducibility in the four-colour theorem", by Robertson, Sanders, Seymour and Thomas
// The library is designed to interface with the Python package configs.py using Python's ctypes package
//
// Created by Dan Romik, October 2023-January 2024
//

// useful links addressing questions that came
// https://www.tutorialspoint.com/how-to-call-a-c-function-in-python
// https://docs.python.org/3/library/ctypes.html
// https://stackoverflow.com/questions/13445568/python-ctypes-how-to-free-memory-getting-invalid-pointer-error

// instructions: 
// -------------
// 1. compile this library with the following command:
// gcc -shared -o libcons.so -fPIC consistent.c -arch x86_64 
// (for use in JupyterLab on my MacBook Pro with Apple M2 Pro processor),
// or
// gcc -shared -o libcons.so -fPIC consistent.c -arch arm64 
// (for use in Python3 running on a terminal on my MacBook Pro with Apple M2 Pro processor)
//

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

#define MAX_RING_SIZE       16
#define MAX_MATCHED_PAIRS   8
static long int numbers_of_noncrossing_matchings[] = { 1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796 }; // Catalan numbers
static long int numbers_of_balanced_signed_matchings[MAX_RING_SIZE+1] = { 
    1, 0, 2, 3, 11, 30, 96, 301, 981, 3228, 10798, 36487, 124543, 428506, 1485004, 5178161, 18155817 
};
static long int numbers_of_canonical_edge_colorings[MAX_RING_SIZE+1] = { 
    0, 1, 2, 5, 14, 41, 122, 365, 1094, 3281, 9842, 29525, 88574, 265721, 797162, 2391485, 7174454
}; // (3^(k-1)+1)/2
static long int powers_of_3[MAX_RING_SIZE+1] = { 
    1, 3, 9, 27, 81, 243, 729, 2187, 6561, 19683, 59049, 177147, 531441, 1594323, 4782969, 14348907, 43046721
};

// a quick and dirty method to generate a Gray code (for order up to 8)
// see OEIS sequence A007814 (https://oeis.org/A007814)
// Mathematica command to generate this sequence:
// Table[IntegerExponent[n, 2], {n, 1, 256}]
// TODO: maybe replace the hard-coded lookup table by a function that computes it dynamically, for greater future flexibility
// in case the value of MAX_RING_SIZE needs to be increased
static int gray_code_flipping_position[1<<MAX_MATCHED_PAIRS] = {
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4,
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5,
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4,
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 6,
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4,
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5,
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4,
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 7,
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4,
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5,
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4,
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 6,
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4,
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5,
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4,
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 
    0 /* in the OEIS sequence this last entry is 8, but here we are doing a Hamiltonian path on a Hamming cube of a particular order, so the sequence of flips is periodic */
      /* also the value of this entry is actually immaterial, the entry is only included to avoid adding a useless conditional inside a loop in the code below */
};


typedef short int signs_bitmask_type; // may change this to int in the future, defining custom type to make the code easy to modify later as needed

typedef struct {
    short int matching[MAX_RING_SIZE];
    signs_bitmask_type signs_as_bitmask;
} signed_matching;

// A macro to compute the number of matched pairs in a signed matching
#define number_of_matched_pairs(simatching) ({ int n = 0; while (n<MAX_MATCHED_PAIRS && simatching.matching[2*n]!=0) n++; n; })


typedef short int bool;
#define FALSE   ((bool)0)
#define TRUE    ((bool)1)

typedef short int edge_coloring_status;  // a bitmask type used for the contents of live_edge_colorings in the function compute_max_consistent_subset()
#define NOT_ALIVE               ((edge_coloring_status)0)
#define ALIVE                   ((edge_coloring_status)1)
#define MARKED_RED              ((edge_coloring_status)2)
#define MARKED_GREEN            ((edge_coloring_status)4)
#define MARKED_BLUE             ((edge_coloring_status)8)
#define ALIVE_AND_MARKED_RGB    (ALIVE | MARKED_RED | MARKED_GREEN | MARKED_BLUE)
#define MARKED_RED_IN_CODE      (2 << 28)   // the color marking bits are stored in bits 28 and above when stored in a marked coloring code
#define MARKED_GREEN_IN_CODE    (4 << 28)
#define MARKED_BLUE_IN_CODE     (8 << 28)
#define MARKED_RGB_IN_CODE      ((MARKED_RED_IN_CODE|MARKED_GREEN_IN_CODE|MARKED_BLUE_IN_CODE) << 28)
#define REMOVE_COLOR_MARKING_BITMASK    ((1<<28)-1)  // bitwise and with this mask to remove the color marking
#define remove_color_marking(marked_code) (marked_code & REMOVE_COLOR_MARKING_BITMASK) // a macro to remove the marking
#define retrieve_color_marking(marked_code) ((marked_code >> 28) & ALIVE_AND_MARKED_RGB) // a macro to recover the marking with the bits in their original positions

#define ADD_COLOR_MARKING           TRUE
#define DO_NOT_ADD_COLOR_MARKING    FALSE

// we're encoding colors as chars with the human-friendly values 'r', 'g', 'b', but in some situations it's convenient to do a conversion 
// to a numerical value: 'r'-->0, 'g'-->1, 'b'-->2, which is what this macro does
#define color_index(color_char) ((color_char) == 'r' ? 0 : ((color_char) == 'g' ? 1 : 2))



int freememory(char *ptr)   // TODO: this doesn't do anything, remove in the future
{
    // printf("freeing pointer: %p\n", ptr);
    // free(ptr);
    return 0;
}


// compute the set of noncrossing matchings of a list of integers and copies the result into results_buffer
// the memory in results_buffer has to be allocated and released by the function calling compute_noncrossing_matchings()
void compute_noncrossing_matchings(short int *numbers_to_match, int min_index, int max_index, short int *results_buffer) {
    if (max_index < min_index + 1)
        return;
    int offset = 0;
    int matching_len = max_index-min_index+1;
    for (int j=min_index+1; j<=max_index; j+=2) {
        int inner_matching_len = j-min_index-1;
        int outer_matching_len = max_index-j;
        int num_inner_matchings_j = numbers_of_noncrossing_matchings[inner_matching_len/2];
        int num_outer_matchings_j = numbers_of_noncrossing_matchings[outer_matching_len/2];
        short int *buffer1 = malloc(num_inner_matchings_j * inner_matching_len * sizeof(short int));
        short int *buffer2 = malloc(num_outer_matchings_j * outer_matching_len * sizeof(short int));
        compute_noncrossing_matchings(numbers_to_match, min_index+1,j-1, buffer1);
        compute_noncrossing_matchings(numbers_to_match, j+1,max_index, buffer2);
        for (int m1=0; m1<num_inner_matchings_j; m1++) {
            for (int m2=0; m2<num_outer_matchings_j; m2++) {
                results_buffer[0 + offset] = numbers_to_match[min_index];
                results_buffer[1 + offset] = numbers_to_match[j];
                for (int k=min_index+1; k<=j-1; k++)
                    results_buffer[k+1-min_index + offset] = buffer1[k-min_index-1 + inner_matching_len * m1];
                for (int k=j+1; k<=max_index; k++)
                    results_buffer[k-min_index + offset] = buffer2[k-j-1 + outer_matching_len * m2];
                offset += matching_len;
            }
        }
        free(buffer1);
        free(buffer2);
    }
}

// compute the set of balanced signed matchings of a given order
// the function balanced_signed_matchings() allocates the memory for the array of signed matchings it returns
// the memory has to be released later by the calling function
signed_matching *balanced_signed_matchings(int order) {
    signed_matching *results_buffer = calloc(numbers_of_balanced_signed_matchings[order], sizeof(signed_matching));
    short int *ncmatchings_buffer = malloc(sizeof(short int) * order * numbers_of_noncrossing_matchings[order >> 1]);
    int number_of_subsets = 1 << order;
    short int subset_elements[order];
    int num_simatchings_recorded = 0;
    for (int subset_bitmask = 1; subset_bitmask < number_of_subsets; subset_bitmask++) {
        // read the binary bits of subset_bitmask and store the 1 values into the array subset_elements
        int number_of_subset_elements = 0;
        int shifted_j = subset_bitmask;
        int bitposition = 1;
        memset(subset_elements, 0, sizeof(short int) * order);
        while (shifted_j != 0) {
            if (shifted_j & 1) {
                subset_elements[number_of_subset_elements] = bitposition;
                number_of_subset_elements++;
            }
            shifted_j >>= 1;
            bitposition++;
        }
        if ((number_of_subset_elements & 1) == 0) {
            // if the number of set bits is even, compute the set of noncrossing matchings with elements taken from the subset we computed
            compute_noncrossing_matchings(subset_elements, 0, number_of_subset_elements-1, ncmatchings_buffer);
            // now copy the matchings obtained from the last function call into the results buffer, each time scanning through all the possible
            // balanced sign choices
            // To do the scan, we start from an initial balanced sign choice ("000...00" or "000...01", whichever of those two is balanced)
            // and then at each iteration flip two bits in accordance with the bit-flipping positions specified in the array
            // gray_code_flipping_position
            int number_of_sign_bitmasks = 1 << ((number_of_subset_elements >> 1)-1);
            int number_of_ncmatchings = numbers_of_noncrossing_matchings[number_of_subset_elements >> 1];
            int parity_for_balanced = order&1;
            for (int ncmatching_index = 0, ncmatchings_buffer_index = 0; ncmatching_index < number_of_ncmatchings; 
                                            ncmatching_index++, ncmatchings_buffer_index += number_of_subset_elements) {
                for (int i = 0, twice_i = 0, sign_bitmask = parity_for_balanced; i < number_of_sign_bitmasks; i++, twice_i += 2) {
                    for (int q=0; q<number_of_subset_elements; q++) {
                        results_buffer[num_simatchings_recorded].matching[q] = ncmatchings_buffer[ncmatchings_buffer_index + q];
                    }
                    results_buffer[num_simatchings_recorded].signs_as_bitmask = sign_bitmask | (i<<16); // TODO: *** experimental - improve ***

                    // now update the bitmask and increment the counter
                    sign_bitmask ^= (1 << gray_code_flipping_position[twice_i]) | (1 << gray_code_flipping_position[twice_i+1]);
                    num_simatchings_recorded++;
                }
            }
        }
    }
    free(ncmatchings_buffer);
    return results_buffer;
}



long int marked_code_of_similar_canonical_edge_coloring_from_weights(int ring_size, long int color_weights[3], bool add_bitmask)
{
    long int code = 0;
    long int min_weight = color_weights[0];
    int min_weight_ind = 0;
    if (color_weights[1]<min_weight) {
        min_weight = color_weights[1];
        min_weight_ind = 1;
    }
    if (color_weights[2]<min_weight) {
        min_weight = color_weights[2];
        min_weight_ind = 2;
    }
    long int max_weight = color_weights[0];
    int max_weight_ind = 0;
    if (color_weights[1]>max_weight) {
        max_weight = color_weights[1];
        max_weight_ind = 1;
    }
    if (color_weights[2]>max_weight) {
        max_weight = color_weights[2];
        max_weight_ind = 2;
    }
    code = (powers_of_3[ring_size]-1)/2 - 2*min_weight - max_weight;

    // now compute a bitmask that will be or'ed with the code to provide additional information about the coloring theta-fitting a signed matching
    // some related definitions:
    static long int color_bitmasks[3] = { MARKED_RED_IN_CODE, MARKED_GREEN_IN_CODE, MARKED_BLUE_IN_CODE };
    static int bitmask_color_choices[3][3] = { { -1, 0, 0 }, { 2, -1, 1 }, { 2, 1, -1 } };

    long int bitmask = 0;   // the variable to store the bitmask
    if (add_bitmask) {
        // there are three scenarios to consider depending on which colors appear in the edge-coloring:
        if (color_weights[0] + color_weights[1] + color_weights[2] == max_weight) {
            // in this scenario all edges are colored with a single color
            bitmask = color_weights[0] == max_weight ? color_bitmasks[0] : (color_bitmasks[1] | color_bitmasks[2]);
        } else if (color_weights[0] == 0) {
            // in this scenario the coloring uses colors 1 ('g') and 2 ('b') but the color 0 ('r') is not used
            bitmask = color_bitmasks[2];
        } else {
            // in this scenario the color 0 ('r') and at least one other color is used
            bitmask = color_bitmasks[bitmask_color_choices[max_weight_ind][min_weight_ind]];
        }
    }
    return code | bitmask;
}

// given an edge-coloring, computes the code of the unique canonical edge-coloring that is similar to it.
long int code_of_similar_canonical_edge_coloring(int ring_size, char *edge_coloring)
{
    long int color_weights[3] = { 0, 0, 0 };
    for (int j=0; j<ring_size; j++)
        color_weights[color_index(edge_coloring[j])] += powers_of_3[j];
    return marked_code_of_similar_canonical_edge_coloring_from_weights(ring_size, color_weights, DO_NOT_ADD_COLOR_MARKING);
}

// compute the set of codes of edge-colorings that fit a given signed matching
// the codes are stored in a buffer that is allocated by marked_codes_of_edge_colorings_that_fit() and returned.
// codes are marked with the possible colors theta such that the edge-coloring associated with the code theta-fits the given signed matching
// the buffer needs to be freed by the calling function
// the number of edge-colorings stored in the buffer is stored in the variable pointed to by the passed argument num_colorings_ptr
long int *marked_codes_of_edge_colorings_that_fit(int ring_size, signed_matching simatching, long int *num_colorings_ptr)
{
    int num_matched_pairs = number_of_matched_pairs(simatching);
    long int num_colorings = 1<<num_matched_pairs;
    *num_colorings_ptr = num_colorings;

    // lazily allocate a memory buffer for the array we'll return, which can be reused in subsequent calls
    static long int *coloring_codes = NULL;
    if (coloring_codes == NULL) 
        coloring_codes = malloc((1<<MAX_MATCHED_PAIRS) * sizeof(long int));

    // fill in the edge-coloring we're calculating with theta='r'
    // this needs to be done only once since the positions where the coloring has 'r's do not change during the enumeration
    char edge_coloring[ring_size];
    for (int k=0; k<ring_size; k++)
        edge_coloring[k] = 'r';
    for (int k=0; k<num_matched_pairs; k++) {
        edge_coloring[simatching.matching[k<<1] - 1] = 'b';
        edge_coloring[simatching.matching[(k<<1)+1] - 1] = ((simatching.signs_as_bitmask>>k)&1) ? 'g' : 'b';
    }
    long int color_weights[3] = { 0, 0, 0 };
    for (int j=0; j<ring_size; j++)
        color_weights[color_index(edge_coloring[j])] += powers_of_3[j];

    // we now iterate over the num_colorings edge-colorings that fit the given signed matching
    // this is done using a Gray code so that we can do an incremental update of the weights at each step to reduce computation time
    bool bit_array[MAX_MATCHED_PAIRS] = { FALSE };
    for (int bit_flipping_counter=0; bit_flipping_counter<num_colorings; bit_flipping_counter++) {
        long int marked_code = marked_code_of_similar_canonical_edge_coloring_from_weights(ring_size, color_weights, ADD_COLOR_MARKING);
        coloring_codes[bit_flipping_counter] = marked_code;

        // now update the bits of the array bit_array and update the weights for use in calculating the next marked code
        int bit_index = gray_code_flipping_position[bit_flipping_counter];  // index of next bit to flip in bit_array
        int twice_bit_index = bit_index<<1;
        int color_position1 = simatching.matching[twice_bit_index] - 1;
        int color_position2 = simatching.matching[twice_bit_index+1] - 1;
        bit_array[bit_index] = !bit_array[bit_index]; // flip the bit, and then switch the colors: 'g' <--> 'b', and update the weights
        if (edge_coloring[color_position1] == 'g') {
            edge_coloring[color_position1] = 'b';
            color_weights[1] -= powers_of_3[color_position1];
            color_weights[2] += powers_of_3[color_position1];
        } else {
            edge_coloring[color_position1] = 'g';
            color_weights[2] -= powers_of_3[color_position1];
            color_weights[1] += powers_of_3[color_position1];
        }
        if (edge_coloring[color_position2] == 'g') {
            edge_coloring[color_position2] = 'b';
            color_weights[1] -= powers_of_3[color_position2];
            color_weights[2] += powers_of_3[color_position2];
        } else {
            edge_coloring[color_position2] = 'g';
            color_weights[2] -= powers_of_3[color_position2];
            color_weights[1] += powers_of_3[color_position2];
        }
    }
    return coloring_codes;
}




// given the code of a canonical edge_coloring, computes the edge-coloring and stores it in the passed character buffer
// the buffer memory has to be provided by the calling function
void compute_canonical_edge_coloring_from_code(int ring_size, char *edge_coloring, long int code)
{
    long int c = code + ((powers_of_3[ring_size]-1)>>1);
    int j = 0;
    for (j=0; j<ring_size; j++) {
        int c_mod_3 = c%3;
        c = c/3;
        edge_coloring[j] = (c_mod_3==1 ? 'r' : (c_mod_3==2 ? 'g' : /* when c_mod_3==0: */ 'b'));
    }
}



char *edge_colorings_buffer;

// an implementation of RSST's algorithm to compute the set of extendable edge-colorings of the ring of a configuration
// (similar to the findlive() function in RSST's reduce.c program, with minor variations)
//
// some notes: 
// 1. the set of colorings is stored in a buffer called edge_colorings_buffer (defined outside the function call as a global variable),
// so that the buffer can be retrived from the Python side in a second function call (the function copy_computed_extendable_edge_colorings
// defined below). Following the second function call, the buffer memory is freed and the variable edge_colorings_buffer is reset to NULL
// 2. the parameters passed to the function are computed on the python side (this has low complexity so there's not much point coding this up in C)
 long int compute_extendable_edge_colorings(int32_t num_vertices, int32_t ring_size, int32_t num_edges, int32_t edge_adjacencies[][4])
{
    bool *edge_colorings = calloc(numbers_of_canonical_edge_colorings[ring_size], sizeof(bool));    // an array to keep track of which edge-colorings are extendable
    long int num_extendable_edge_colorings = 0; // keep track of how many extendable edge-colorings we recorded (useful for debugging)

    int n = num_vertices;
    int r = ring_size;
    int m = 3*n-3-r;
    int c[m];   // this is the array where we'll store the tricoloring of the configuration being scanned through. The values for the three colors are 1,2,4 (powers of 2 so we can use bitwise operations for a small efficiency gain)
    for (int j=0; j<m; j++) {   // zero out the array to start
        c[j] = 0;
    }
    c[m-1] = 1; // we fix the colors of the last and next to last edge to 1 and 2
    c[m-2] = 2;
    c[m-3] = 1;
    int forbidden[m-2];    // called F in the paper, forbidden in RSST's reduce.c program
    for (int j=0; j<m-2; j++) {
        forbidden[j] = 0;
    }
    int j = m-2;

    char *powerof2_to_color_permutations[6] = { "_rg_b", "_rb_g", "_gr_b", "_bg_r", "_gb_r", "_br_g" };
    //  TODO: in the current implementation I think it's not necessary to ensure the edge-coloring is canonical, since we're passing it
    // through a call to code_of_similar_canonical_edge_coloring(), which returns a code of a canonical edge-coloring
    // use this to get rid of this array of 6 permutations at some point and simplify the code a bit (testing to make sure everything still works)

    // compute the forbidden colors for the initial edge with index m-2. This is a set of colors from 1,2,4 so can be conveniently stored as a bit mask
    for (int k=0; k<4; k++) {
        if (edge_adjacencies[j-1][k]>j-1)
            forbidden[j-1] |= c[edge_adjacencies[j-1][k]];
    }

    // the main loop of the depth-first search
    while (TRUE) {
        // look for an available color for the current edge
        while ((c[j-1] & forbidden[j-1]) && (c[j-1] < 8)) {
            c[j-1] <<= 1;
        }

        if (c[j-1]==8) { // there is no available color, which means we have to backtrack up the tree
            j++;
            if (j>=m-1) { // we came back to the root, so the depth first traversal of the tree is complete
                // the remaining work to do is to represent the output as an array of c strings convenient to pass back
                // to Python, and store it in the globally accessible edge_colorings_buffer variable
                edge_colorings_buffer = malloc(num_extendable_edge_colorings * (ring_size+1) + 1);
                char *current_char_ptr = edge_colorings_buffer;
                char ec[MAX_RING_SIZE+1];
                ec[ring_size] = 0;
                for (long int i=0; i<numbers_of_canonical_edge_colorings[ring_size]; i++) {
                    if (edge_colorings[i]) {
                        compute_canonical_edge_coloring_from_code(ring_size, ec, i);
                        for (int k=0; k<ring_size; k++) {
                            *current_char_ptr = ec[k];
                            current_char_ptr++;
                        }
                        *current_char_ptr = '\n';
                        current_char_ptr++;
                    }
                }
                free(edge_colorings);   // don't need this anymore

                // return the number of extendable edge-colorings so that on the Python side we'll know the size of the memory buffer that needs to be allocated
                return num_extendable_edge_colorings;   
            }
            c[j-1] <<= 1; // cycle to the next color for this edge and go back to the beginning of the main while loop
        }
        else if (j>r+1) { // we found a valid color but we're not done yet with this attempted coloring
            j--; // move on to the next edge in need of coloring
            c[j-1] = 1; // after going down one level in the tree, always start from the color 1
            // make a list of forbidden colors for this edge based on the edges already colored
            forbidden[j-1] = 0;
            for (int k=0; k<4; k++) {
                if (edge_adjacencies[j-1][k]>j-1)
                    forbidden[j-1] |= c[edge_adjacencies[j-1][k]];
            }
        }
        else { // else if (j==r+1) {     // we found a valid color and it's the last edge that needed to be colored
                // compute the colors for the ring edges based on the internal edge colors
                for (int i=0; i<r; i++) { 
                    // each ring edge shares a triangle with two already colored internal edges
                    c[i] = 7 - c[edge_adjacencies[i][0]] - c[edge_adjacencies[i][1]];
                }

                // we need to permute the colors 1,2,4 to ensure the coloring we are recording is canonical,
                // here we identify the correct permutation to use:
                // TODO: as mentioned above, this seems unnecessary - improve
                int lastc = c[r-1];
                int x = r-2;
                while (x>=0 && c[x]==c[r-1])
                    x--;
                int secondlastc = x==-1 ? lastc : c[x];
                int permutations_matrix[3][3] = { {0,0,1}, {2,2,5}, {4,3,3} };
                int inds[] = { -1,0,1,-1,2 };
                int perm_ind = permutations_matrix[inds[lastc]][inds[secondlastc]];

                // create the edge-coloring string and calculate its code
                char edge_coloring_string[MAX_RING_SIZE];
                for (int i=0; i<ring_size; i++)
                    edge_coloring_string[i] = powerof2_to_color_permutations[perm_ind][c[i]];

                long int edge_coloring_code = code_of_similar_canonical_edge_coloring(ring_size, edge_coloring_string);

                // record the edge coloring
                if (edge_colorings[edge_coloring_code] == FALSE) {
                    edge_colorings[edge_coloring_code] = TRUE;
                    num_extendable_edge_colorings++;
                }
                c[j-1] <<= 1; // after recording this coloring, cycle to the next color for this edge
        }
    }   // end of main loop
}

// TODO: needing two function calls is a clunky solution to the problem of freeing up the buffer. Find a better solution
// where everything gets done with one function call
void copy_computed_extendable_edge_colorings(char *buffer, int num_bytes_to_copy) 
{
    // memcpy(buffer, edge_colorings_buffer, num_bytes_to_copy);
    for (int j=0; j<num_bytes_to_copy; j++) {
        buffer[j] = edge_colorings_buffer[j];
    }
    free(edge_colorings_buffer);
    edge_colorings_buffer = NULL;
}






// // this function computes the maximal consistent subset of the set of non-extendable edge colorings
// // as arguments it receives: the ring size, number of canonical extendable edge colorings, and a linear buffer with the
// // set of canonical extendable edge colorings, where each edge coloring is stored as a list of characters of length ring_size
// // taken from 'r','g','b'
int compute_max_consistent_subset(int ring_size, long int num_extendable_edge_colorings, char *extendable_edge_colorings, char *output_buffer)
{
    static signed_matching *all_balanced_matchings_by_ring_size[MAX_RING_SIZE] = { NULL };

    long int num_edge_colorings = numbers_of_canonical_edge_colorings[ring_size];
    long int num_balanced_signed_matchings = numbers_of_balanced_signed_matchings[ring_size];

    // lazily calculate the set of balanced signed matchings for the given ring size (retaining the result for subsequent calls)
    if (all_balanced_matchings_by_ring_size[ring_size] == NULL)
        all_balanced_matchings_by_ring_size[ring_size] = balanced_signed_matchings(ring_size);
    signed_matching *all_balanced_signed_matchings = all_balanced_matchings_by_ring_size[ring_size];

    // lazily allocate the arrays for keeping track of live edge-colorings and balanced signed matchings
    static edge_coloring_status *live_edge_colorings = NULL; 
    static bool *live_signed_matchings = NULL; 
    if (live_edge_colorings == NULL)
        live_edge_colorings = malloc(sizeof(edge_coloring_status) * numbers_of_canonical_edge_colorings[MAX_RING_SIZE]);
    if (live_signed_matchings == NULL)
        live_signed_matchings = malloc(sizeof(bool) * numbers_of_balanced_signed_matchings[MAX_RING_SIZE]);

    // mark all edge-colorings and signed matchings as live initially
    for (long int i=0; i < num_edge_colorings; i++)
        live_edge_colorings[i] = ALIVE;
    for (long int i=0; i < num_balanced_signed_matchings; i++)
        live_signed_matchings[i] = TRUE;

    // for all extendable edge-colorings, compute their code and mark all corresponding positions in the live edge colorings array as "dead"
    for (long int i=0; i<num_extendable_edge_colorings; i++) {
        long int code = code_of_similar_canonical_edge_coloring(ring_size, extendable_edge_colorings + i*ring_size*sizeof(char));
        live_edge_colorings[code] = NOT_ALIVE;
    }
    // at this point, only the non-extendable edge colorings are marked as alive

    long int num_live_edge_colorings = num_edge_colorings - num_extendable_edge_colorings;
    long int num_live_signed_matchings = num_balanced_signed_matchings;

    // The main loop - compute the sets \mathcal{M}_{i+1} and \mathcal{C}_{i+1} from the sets \mathcal{M}_i and \mathcal{C}_i
    while (TRUE) {
        sprintf(output_buffer+strlen(output_buffer), "%ld,%ld,", num_live_signed_matchings, num_live_edge_colorings);

        // compute \mathcal{M}_{i+1}:
        // \mathcal{M}_{i+1} is the set of all signed matchings sm in \mathcal{M}_i for which for every coloring c,
        // if there exists a theta such that c theta-fits sm then c is in \mathcal{C}_i
        for (long int i=0; i < num_balanced_signed_matchings; i++) {
            if (live_signed_matchings[i]) {
                signed_matching simatching = all_balanced_signed_matchings[i];
                long int num_colorings_that_fit;
                long int *marked_codes_of_colorings_that_fit = marked_codes_of_edge_colorings_that_fit(ring_size, simatching, &num_colorings_that_fit);
                bool for_loop_breaking_flag = FALSE;
                for (long int j=0; j<num_colorings_that_fit; j++) {
                    long int code=remove_color_marking(marked_codes_of_colorings_that_fit[j]);
                    if (live_edge_colorings[code] == NOT_ALIVE) {
                        live_signed_matchings[i] = FALSE;   // signed matching didn't pass the test, mark it as dead
                        num_live_signed_matchings--;
                        for_loop_breaking_flag = TRUE;
                        break;
                    }
                }

                // if the signed matching is still alive, mark the edge colorings that theta-fit it for some theta with the possible
                // colors theta that it theta-fits. This information makes it easy to compute \mathcal{C}_{i+1}, as is done below
                if (!for_loop_breaking_flag) {
                    for (long int j=0; j<num_colorings_that_fit; j++) {
                        long int marked_code=marked_codes_of_colorings_that_fit[j];
                        long int code=remove_color_marking(marked_code);
                        live_edge_colorings[code] |= retrieve_color_marking(marked_code);
                    }
                }
                // in the current version the buffer is allocated and then never freed for efficiency,
                // this is okay since the size of the buffer is 2 to the power of MAX_MATCHED_PAIRS times sizeof(long int),
                // so 1024 bytes - nothing to worry about
                // free(marked_codes_of_colorings_that_fit);    // TODO: delete this at some point...
            }
        }

        // compute \mathcal{C}_{i+1}:
        // \mathcal{C}_{i+1} is the set of all colorings c in \mathcal{C}_i for which for every theta there exists
        // a signed matching sm in \mathcal{M}_{i+1} such that c theta-fits sm
        // With the marking information collected above, this simply means going through all live edge colorings and inspecting their status
        long int prev_num_live_edge_colorings = num_live_edge_colorings;
        for (long int j=0; j<num_edge_colorings; j++) {
            if (live_edge_colorings[j] != NOT_ALIVE) {
                if (live_edge_colorings[j] == ALIVE_AND_MARKED_RGB) {
                    live_edge_colorings[j] = ALIVE; // remove the color markings, to get things ready for the next iteration of the main loop
                } else {
                    live_edge_colorings[j] = NOT_ALIVE;     // the edge coloring failed the test, mark it as dead
                    num_live_edge_colorings--;
                }
            }
        }

        if (num_live_edge_colorings == prev_num_live_edge_colorings) {
            sprintf(output_buffer+strlen(output_buffer), num_live_edge_colorings == 0 ? "D-reducible" : "not-D-reducible");
            // note:
            // in the current version I'm not freeing up these buffers since in a typical use the function compute_max_consistent_subset()
            // is called many times in successions, so we may as well allocate the buffers once and then reuse them
            //
            // free(live_edge_colorings);
            // free(live_signed_matchings);
            // free(all_balanced_signed_matchings); 
            return 0;
        }
    }
}










typedef struct {
    short int bitmask;
    short int number_of_moves_to_win;
} edge_coloring_game_data;

#define UNKNOWN_NUMBER_OF_MOVES     (-1)
// #define NOT_ALIVE               ((edge_coloring_status)0)
// #define ALIVE                   ((edge_coloring_status)1)
// #define MARKED_RED              ((edge_coloring_status)2)
// #define MARKED_GREEN            ((edge_coloring_status)4)
// #define MARKED_BLUE             ((edge_coloring_status)8)
// #define ALIVE_AND_MARKED_RGB    (ALIVE | MARKED_RED | MARKED_GREEN | MARKED_BLUE)
// #define MARKED_RED_IN_CODE      (2 << 28)   // the color marking bits are stored in bits 28 and above when stored in a marked coloring code
// #define MARKED_GREEN_IN_CODE    (4 << 28)
// #define MARKED_BLUE_IN_CODE     (8 << 28)
// #define MARKED_RGB_IN_CODE      ((MARKED_RED_IN_CODE|MARKED_GREEN_IN_CODE|MARKED_BLUE_IN_CODE) << 28)
// #define REMOVE_COLOR_MARKING_BITMASK    ((1<<28)-1)  // bitwise and with this mask to remove the color marking
// #define remove_color_marking(marked_code) (marked_code & REMOVE_COLOR_MARKING_BITMASK) // a macro to remove the marking
// #define retrieve_color_marking(marked_code) ((marked_code >> 28) & ALIVE_AND_MARKED_RGB) // a macro to recover the marking with the bits in their original positions

// #define ADD_COLOR_MARKING           TRUE
// #define DO_NOT_ADD_COLOR_MARKING    FALSE







// a new version of the compute_max_consistent_subset() function where the calculation is reframed as an analysis of the optimal
// strategy in a color switching game
int analyze_color_switching_game(int ring_size, long int num_extendable_edge_colorings, char *extendable_edge_colorings, char *output_buffer)
{
    static signed_matching *all_balanced_matchings_by_ring_size[MAX_RING_SIZE] = { NULL };

    long int num_edge_colorings = numbers_of_canonical_edge_colorings[ring_size];
    long int num_balanced_signed_matchings = numbers_of_balanced_signed_matchings[ring_size];

    // lazily calculate the set of balanced signed matchings for the given ring size (retaining the result for subsequent calls)
    if (all_balanced_matchings_by_ring_size[ring_size] == NULL)
        all_balanced_matchings_by_ring_size[ring_size] = balanced_signed_matchings(ring_size);
    signed_matching *all_balanced_signed_matchings = all_balanced_matchings_by_ring_size[ring_size];

    // lazily allocate the arrays for keeping track of live edge-colorings and balanced signed matchings
    static edge_coloring_game_data *edge_colorings_data = NULL; 
    static bool *live_signed_matchings = NULL; 
    if (edge_colorings_data == NULL)
        edge_colorings_data = malloc(sizeof(edge_coloring_game_data) * numbers_of_canonical_edge_colorings[MAX_RING_SIZE]);
    if (live_signed_matchings == NULL)
        live_signed_matchings = malloc(sizeof(bool) * numbers_of_balanced_signed_matchings[MAX_RING_SIZE]);

    // initialize the arrays edge_colorings_data and live_signed_matchings
    for (long int i=0; i < num_edge_colorings; i++) {
        edge_colorings_data[i].bitmask = 0;
        edge_colorings_data[i].number_of_moves_to_win = UNKNOWN_NUMBER_OF_MOVES;
    }
    for (long int i=0; i < num_balanced_signed_matchings; i++)
        live_signed_matchings[i] = TRUE;

    // for all extendable edge-colorings, compute their code and mark all corresponding positions in the edge_colorings_data as being
    // winning positions with 0 moves to win
    for (long int i=0; i<num_extendable_edge_colorings; i++) {
        long int code = code_of_similar_canonical_edge_coloring(ring_size, extendable_edge_colorings + i*ring_size*sizeof(char));
        edge_colorings_data[code].number_of_moves_to_win = 0;
    }


    long int num_not_yet_winning_edge_colorings = num_edge_colorings - num_extendable_edge_colorings;
    long int num_live_signed_matchings = num_balanced_signed_matchings;

    // The main loop - compute the sets \mathcal{M}_{i+1} and \mathcal{C}_{i+1} from the sets \mathcal{M}_i and \mathcal{C}_i
    for (int number_of_moves = 1; TRUE; number_of_moves++) {
        sprintf(output_buffer+strlen(output_buffer), "%ld,%ld,", num_live_signed_matchings, num_not_yet_winning_edge_colorings);

        // compute \mathcal{M}_{i+1}:
        // \mathcal{M}_{i+1} is the set of all signed matchings sm in \mathcal{M}_i for which for every coloring c,
        // if there exists a theta such that c theta-fits sm then c is in \mathcal{C}_i
        for (long int i=0; i < num_balanced_signed_matchings; i++) {
            if (live_signed_matchings[i]) {
                signed_matching simatching = all_balanced_signed_matchings[i];
                long int num_colorings_that_fit;
                long int *marked_codes_of_colorings_that_fit = marked_codes_of_edge_colorings_that_fit(ring_size, simatching, &num_colorings_that_fit);
                bool for_loop_breaking_flag = FALSE;
                for (long int j=0; j<num_colorings_that_fit; j++) {
                    long int code=remove_color_marking(marked_codes_of_colorings_that_fit[j]);
                    if (edge_colorings_data[code].number_of_moves_to_win != UNKNOWN_NUMBER_OF_MOVES) {
                        live_signed_matchings[i] = FALSE;   // signed matching didn't pass the test, mark it as dead
                        num_live_signed_matchings--;
                        for_loop_breaking_flag = TRUE;
                        break;
                    }
                }

                // if the signed matching is still alive, mark the edge colorings that theta-fit it for some theta with the possible
                // colors theta that it theta-fits. This information makes it easy to compute \mathcal{C}_{i+1}, as is done below
                if (!for_loop_breaking_flag) {
                    for (long int j=0; j<num_colorings_that_fit; j++) {
                        long int marked_code=marked_codes_of_colorings_that_fit[j];
                        long int code=remove_color_marking(marked_code);
                        edge_colorings_data[code].bitmask |= retrieve_color_marking(marked_code);
                    }
                }
                // in the current version the buffer is allocated and then never freed for efficiency,
                // this is okay since the size of the buffer is 2 to the power of MAX_MATCHED_PAIRS times sizeof(long int),
                // so 1024 bytes - nothing to worry about
                // free(marked_codes_of_colorings_that_fit);    // TODO: delete this at some point...
            }
        }

        // compute \mathcal{C}_{i+1}:
        // \mathcal{C}_{i+1} is the set of all colorings c in \mathcal{C}_i for which for every theta there exists
        // a signed matching sm in \mathcal{M}_{i+1} such that c theta-fits sm
        // With the marking information collected above, this simply means going through all live edge colorings and inspecting their status
        long int prev_num_not_yet_winning_edge_colorings = num_not_yet_winning_edge_colorings;
        for (long int j=0; j<num_edge_colorings; j++) {
            if (edge_colorings_data[j].number_of_moves_to_win == UNKNOWN_NUMBER_OF_MOVES) {
                if (edge_colorings_data[j].bitmask == (MARKED_RED | MARKED_GREEN | MARKED_BLUE)) {
                    edge_colorings_data[j].bitmask = 0; // remove the color markings, to get things ready for the next iteration of the main loop
                } else {
                    // TODO: "winning theta" below is not necessarily the best thing to record, possibly would be nicer to determine the "best theta"?
                    edge_colorings_data[j].number_of_moves_to_win = number_of_moves;     // the edge coloring is a winning position, record the number of moves
                    edge_colorings_data[j].bitmask = 7 - (edge_colorings_data[j].bitmask >> 1);    // the bitmask now represents the "winning theta" color-selection moves
                    num_not_yet_winning_edge_colorings--;
                }
            }
        }

        if (num_not_yet_winning_edge_colorings == prev_num_not_yet_winning_edge_colorings) {
            sprintf(output_buffer+strlen(output_buffer), num_not_yet_winning_edge_colorings == 0 ? "D-reducible" : "not-D-reducible");

            // now record the "winning theta" info associated with each edge coloring
            sprintf(output_buffer+strlen(output_buffer), "***");    // a delimiter so that on the Python side it will be easy to tell where this part of the output starts
            char *sub_buffer1 = output_buffer+strlen(output_buffer);
            char bitmask_to_char[8] = { '0', '1', '2', '3', '4', '5', '6', '7' };
            for (long int j=0; j<num_edge_colorings; j++) {
                sub_buffer1[j] = bitmask_to_char[edge_colorings_data[j].bitmask];
            }

            // now record the number of moves info associated with each edge coloring
            char *sub_buffer2 = sub_buffer1 + num_edge_colorings;
            sprintf(sub_buffer2, "***");    // a delimiter
            sub_buffer2 += 3;
            for (long int j=0; j<num_edge_colorings; j++) {
                if (j==num_edge_colorings-1)
                    sprintf(sub_buffer2, "%d", edge_colorings_data[j].number_of_moves_to_win);
                else
                    sprintf(sub_buffer2, "%d,", edge_colorings_data[j].number_of_moves_to_win);
                sub_buffer2 += strlen(sub_buffer2);
            }

            // note:
            // in the current version I'm not freeing up these buffers since in a typical use the function compute_max_consistent_subset()
            // is called many times in successions, so we may as well allocate the buffers once and then reuse them
            //
            // free(live_edge_colorings);
            // free(live_signed_matchings);
            // free(all_balanced_signed_matchings); 
            return 0;
        }
    }
}






// produce a human-readable string with the list of noncrossing matchings
// (useful for debugging, not really for anything else)
char *noncrossing_matchings_cstring(int order) {
    short int *results_buffer = malloc(sizeof(short int) * 2*order * numbers_of_noncrossing_matchings[order]);
    short int numbers_to_match[] = { 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18 };
    compute_noncrossing_matchings(numbers_to_match, 0,2*order-1, results_buffer);
    char *results_string = malloc(3*sizeof(short int) * 2*order * numbers_of_noncrossing_matchings[order]);
    char *sprintf_here = results_string;
    for (int m=0; m<numbers_of_noncrossing_matchings[order]; m++) {
        for (int j=0; j<2*order; j++) {
            if (j<2*order-1)
               sprintf_here += sprintf(sprintf_here, "%d,", results_buffer[2*order * m + j]);
            else
                sprintf_here += sprintf(sprintf_here, "%d", results_buffer[2*order * m + j]);
        }
        if (m<numbers_of_noncrossing_matchings[order]-1)
            sprintf_here += sprintf(sprintf_here, "\n");
    }
    free(results_buffer);
    return results_string; // note: the buffer was allocated but not freed
}

// produce a human-readable string with the list of balanced signed matchings
// (useful for debugging, not really for anything else)
char *balanced_signed_matchings_cstring(int order) {
    signed_matching *results_buffer = balanced_signed_matchings(order);
    char *results_string = malloc(5*numbers_of_balanced_signed_matchings[order]*sizeof(signed_matching)); // TODO: no matching call to free()
    char *sprintf_here = results_string;
    for (long int m=0; m<numbers_of_balanced_signed_matchings[order]; m++) {
        sprintf_here += sprintf(sprintf_here, "%4ld   matching: ", m+1);
        int ncmatching_order = -1;
        for (int j=0; j<order; j++) {
            if (results_buffer[m].matching[j]==0) {
                if (ncmatching_order == -1) {
                    ncmatching_order = j>>1;
                }
                if (j<order-1)
                    sprintf_here += sprintf(sprintf_here, "  ");
                else
                    sprintf_here += sprintf(sprintf_here, "   signs: ");
            }
            else {
                sprintf_here += sprintf(sprintf_here, "%d", results_buffer[m].matching[j]);
                if (j<order-1)
                    sprintf_here += sprintf(sprintf_here, ",");
                else
                    sprintf_here += sprintf(sprintf_here, "  signs: ");
            }
        }

        int flag = 0;
        if (ncmatching_order == -1)
            ncmatching_order = order>>1;
        for (int j=0; j<MAX_MATCHED_PAIRS; j++) {
            if (j==ncmatching_order) {
                flag = 1;
                sprintf_here += sprintf(sprintf_here, "\n");
                break;
            }
            sprintf_here += sprintf(sprintf_here, "%s", ((results_buffer[m].signs_as_bitmask >> j)&1) == 0 ? "+1" : "-1");
            if (j<MAX_MATCHED_PAIRS-1 && j!=ncmatching_order-1)
                sprintf_here += sprintf(sprintf_here, ",");
        }

        if (!flag && m<numbers_of_noncrossing_matchings[order]-1)
            sprintf_here += sprintf(sprintf_here, "\n");
    }
    free(results_buffer);
    return results_string;
}




// *** this function is no longer necessary - commenting out ***
// check whether a given edge-coloring theta-fits a given signed matching, for a given value of theta
// bool check_theta_fit(short int ring_size, char *edge_coloring, char theta, signed_matching *simatching_ptr) {

//     bool matched_edges[ring_size];
//     for (int i=0; i<ring_size; i++)
//         matched_edges[i] = FALSE;

//     // go through the matched pairs and test if the colors of the edges being matched meet the conditions for theta-fitting
//     // at the same time, record which edges were matched to use in an additional check later
//     for (int j=0, two_j=0; j<MAX_MATCHED_PAIRS; j++, two_j+=2) {
//         if ((*simatching_ptr).matching[two_j] == 0)
//             break;

//         char first_matched_edge_color = edge_coloring[(*simatching_ptr).matching[two_j]-1];
//         char second_matched_edge_color = edge_coloring[(*simatching_ptr).matching[two_j+1]-1];
//         if (first_matched_edge_color==theta || second_matched_edge_color==theta)
//             return FALSE; // if any edges that are matched are colored theta, the condition for theta-fitting is not met

//         // for theta-fitting to hold, any two edges that are matched have the same color iff the corresponding sign in the bit mask
//         // is associated with the sign "+1"
//         // note: as one can see from the code in the function balanced_signed_matchings_cstring() above, in the encoding
//         // of signed matchings, a bit of "0" in the bit mask is associated with the sign "+1" and a bit of "1" in the bit mask
//         // is associated with the sign "-1"
//         // TODO: clean up the code to avoid this potentially confusing encoding or to document it better
//         bool sign_is_minus_one = ((((*simatching_ptr).signs_as_bitmask>>j)&1) == 1);
//         if ((sign_is_minus_one && (first_matched_edge_color==second_matched_edge_color))
//             || ((!sign_is_minus_one) && (first_matched_edge_color!=second_matched_edge_color)))
//             return FALSE; // failed the test for theta-fitting

//         matched_edges[(*simatching_ptr).matching[two_j]-1] = TRUE;
//         matched_edges[(*simatching_ptr).matching[two_j+1]-1] = TRUE;
//     }

//     // the final way that we might fail the test for theta-fitting is if an edge whose color is not theta
//     // did not appear as part of a matched pair 
//     for (int i=0; i<ring_size; i++) {
//         if ((!matched_edges[i]) && edge_coloring[i]!=theta)
//             return FALSE;
//     }

//     // if we reached this point, all conditions for theta-fitting were met, so return TRUE
//     return TRUE;
// }


// *** an older version of compute_max_consistent_subset with a more naive and much slower algorithm ***
// int compute_max_consistent_subset_old(int ring_size, long int num_extendable_edge_colorings, char *extendable_edge_colorings)
// {
//     long int num_edge_colorings = numbers_of_canonical_edge_colorings[ring_size];
//     long int num_balanced_signed_matchings = numbers_of_balanced_signed_matchings[ring_size];

//     signed_matching *all_balanced_signed_matchings = balanced_signed_matchings(ring_size);

//     // allocate the arrays for keeping track of live edge-colorings and balanced signed matchings
//     bool *live_edge_colorings = malloc(sizeof(bool) * num_edge_colorings);
//     bool *live_signed_matchings = malloc(sizeof(bool) * num_balanced_signed_matchings);

//     // mark all edge-colorings and signed matchings as live initially
//     for (long int i=0; i < num_edge_colorings; i++)
//         live_edge_colorings[i] = TRUE;
//     for (long int i=0; i < num_balanced_signed_matchings; i++)
//         live_signed_matchings[i] = TRUE;

//     // for all extendable edge-colorings, compute their code and mark all corresponding positions in the live edge colorings array as "dead"
//     for (long int i=0; i<num_extendable_edge_colorings; i++) {
//         long int code = code_of_similar_canonical_edge_coloring(ring_size, extendable_edge_colorings + i*ring_size*sizeof(char));
//         live_edge_colorings[code] = FALSE;
//     }
//     // at this point, only the non-extendable edge colorings are marked as live

//     // The main loop - compute the sets \mathcal{M}_{i+1} and \mathcal{C}_{i+1} from the sets \mathcal{M}_i and \mathcal{C}_i
//     long int num_live_edge_colorings = num_edge_colorings - num_extendable_edge_colorings;
//     long int num_live_signed_matchings = num_balanced_signed_matchings;

//     int step_num = 0;
//     while (TRUE) {
//         printf("step i=%d:  |C(%d)|=%-4ld |M(%d)|=%-4ld\n", step_num, step_num, num_live_edge_colorings, step_num, num_live_signed_matchings);

//         // compute \mathcal{M}_{i+1}:
//         // \mathcal{M}_{i+1} is the set of all signed matchings sm in \mathcal{M}_i for which for every coloring c,
//         // if there exists a theta such that c theta-fits sm then c is in \mathcal{C}_i
//         for (long int i=0; i < num_balanced_signed_matchings; i++) {
//             if (live_signed_matchings[i]) {
//                 signed_matching simatching = all_balanced_signed_matchings[i];
//                 long int num_colorings_that_fit;
//                 long int *codes_of_colorings_that_fit = codes_of_edge_colorings_that_fit(ring_size, simatching, &num_colorings_that_fit);
//                 for (long int j=0; j<num_colorings_that_fit; j++) {
//                     long int code=codes_of_colorings_that_fit[j];
//                     if (!(live_edge_colorings[code])) {
//                         live_signed_matchings[i] = FALSE;   // signed matching didn't pass the test, mark it as dead
//                         num_live_signed_matchings--;
//                         break;
//                     }
//                 }
//                 free(codes_of_colorings_that_fit);
//             }
//         }
        
//         // compute \mathcal{C}_{i+1}:
//         // \mathcal{C}_{i+1} is the set of all colorings c in \mathcal{C}_i for which for every theta there exists
//         // a signed matching sm in \mathcal{M}_{i+1} such that c theta-fits sm
//         long int prev_num_live_edge_colorings = num_live_edge_colorings;

//         char current_edge_coloring[ring_size];

//         for (long int j=0; j<num_edge_colorings; j++) {
//             if (live_edge_colorings[j]) {
//                 bool found_red_fit = FALSE;
//                 bool found_green_fit = FALSE;
//                 bool found_blue_fit = FALSE;
//                 bool edge_coloring_stays_live = FALSE;
//                 compute_canonical_edge_coloring_from_code(ring_size, current_edge_coloring, j);
//                 for (long int i=0; i < num_balanced_signed_matchings; i++) {
//                     if (live_signed_matchings[i]) {
//                         if (!found_red_fit &&
//                             check_theta_fit(ring_size, current_edge_coloring, 'r', &(all_balanced_signed_matchings[i]))) {
//                             found_red_fit = TRUE;
//                         }
//                         if (!found_green_fit &&
//                             check_theta_fit(ring_size, current_edge_coloring, 'g', &(all_balanced_signed_matchings[i]))) {
//                             found_green_fit = TRUE;
//                         }
//                         if (!found_blue_fit &&
//                             check_theta_fit(ring_size, current_edge_coloring, 'b', &(all_balanced_signed_matchings[i]))) {
//                             found_blue_fit = TRUE;
//                         }

//                         if (found_red_fit && found_green_fit && found_blue_fit) {
//                             edge_coloring_stays_live = TRUE;
//                             break;  // the edge coloring passed the test, we can stop scanning through the signed matchings
//                         }
//                     }
//                 }
//                 if (!edge_coloring_stays_live) {
//                     live_edge_colorings[j] = FALSE;   // the edge coloring failed the test, mark it as dead
//                     num_live_edge_colorings--;
//                 }
//             }
//         }

//         if (num_live_edge_colorings == prev_num_live_edge_colorings) {
//             printf("*** maximal consistent subset has %ld edge colorings ***\n\n", num_live_edge_colorings);
//             free(live_edge_colorings);
//             free(live_signed_matchings);
//             free(all_balanced_signed_matchings);
//             return 0;
//         }
//         step_num++;
//     }
// }






