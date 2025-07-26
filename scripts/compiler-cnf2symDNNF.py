"This script needs to be runned from the folder where this file is in"


import os

import time

import sys

input = sys.argv[1]

input_folder_file = os.path.split(input)

input_folder = input_folder_file[0]
input_file = input_folder_file[1]

filename = os.path.splitext(input_file)[0]

startTime = time.time()
os.system('./../build/sym_ganak -q '+str(input))
halfTime = time.time()
os.system('python trace2symDNNF.py')
endTime = time.time()


os.system('mv output.nnf ../results/'+filename+'.nnf')
print("\nsymDNNF printed to ../results/"+filename+".nnf\n\n")

# gather statistics on symDNNF
file = '../results/'+filename+'.nnf'

f = open(file, "r")
line = f.readline()
f.close()
info = line.split()
nodes = info[1]
edges = info[2]
permutation_size = info[4]

print("===============================================")
print("               COMPILATION STATS               ")
print("===============================================")
print("compilation time\t\t",endTime-startTime)
print(" of which trace conversion time\t",endTime-halfTime)
print("nodes\t\t\t\t",nodes)
print("edges\t\t\t\t",edges)
print("permutation size\t\t",permutation_size)
print("===============================================")