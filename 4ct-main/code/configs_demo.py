from tqdm import tqdm
import ctypes
import os

libcons=ctypes.CDLL('./libcons.so')


def demo_count_extendable_colorings_slow(configs):
    num_confs = len(configs)
    coloring_counts = []
    configs_progress_bar = tqdm(configs, desc="Counting extendable colorings...")
    for conf in configs_progress_bar:
        count = len(conf.extendable_edge_coloring_strings_slow())
        configs_progress_bar.set_description(f"Counting extendable colorings (last count={count})")
        coloring_counts.append(count)
    return coloring_counts


def demo_count_extendable_colorings(configs):
    num_confs = len(configs)
    coloring_counts = []
    configs_progress_bar = tqdm(configs, desc="Counting extendable colorings...")
    for conf in configs_progress_bar:
        count = len(conf.extendable_edge_coloring_strings())
        configs_progress_bar.set_description(f"Counting extendable colorings (last count={count})")
        coloring_counts.append(count)
    return coloring_counts



def demo_check_reducibility(configs):
    configs_progress_bar = tqdm(configs, desc="Checking reducibility (DR)...")
    for conf in configs_progress_bar:
        conf.compute_max_consistent_subset()
        configs_progress_bar.set_description(f"Checking reducibility (DR)... (last ring size={conf.ring_size})")

def demo_check_reducibility_rsst(configs):
    configs_progress_bar = tqdm(configs, desc="Checking reducibility (RSST)...")
    for conf in configs_progress_bar:
        conf.compute_max_consistent_subset_rsst()
        configs_progress_bar.set_description(f"Checking reducibility (RSST)... (last ring size={conf.ring_size})")





''' Definitions related to the C library libcons.so
'''
# a python wrapper for the function libcons.noncrossing_matchings_string()
libcons.noncrossing_matchings_cstring.restype = ctypes.c_char_p
def noncrossing_matchings_string(order):
    bytes = libcons.noncrossing_matchings_cstring(order)
    string = bytes.decode('utf-8')
    libcons.freememory(bytes)   # TODO: this doesn't do anything, so there is currently a memory leak - improve
    return string

# a python wrapper for the function libcons.balanced_signed_matchings_cstring()
libcons.balanced_signed_matchings_cstring.restype = ctypes.c_char_p
def balanced_signed_matchings_string(order):
    bytes = libcons.balanced_signed_matchings_cstring(order)
    string = bytes.decode('utf-8')
    libcons.freememory(bytes)   # TODO: this doesn't do anything, so there is currently a memory leak - improve
    return string

def compile_libcons():
    os.system("gcc -shared -o libcons.so -fPIC consistent.c -arch x86_64")