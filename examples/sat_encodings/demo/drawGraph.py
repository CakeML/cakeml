import networkx as nx

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

import re

print("Visualizing Graph")

f = open("graphSolution.txt", "r")
rows = f.readlines()

input = []
for row in rows:
    row1 = row.strip(' [],\n')
    r = re.split(', \[|], ', row1)
    r[0] = int(r[0])
    r[1] = r[1].split(',')
    r[1] = [int(n) for n in r[1]]
    input.append(r)

f.close()

print(input)

nodes = [row[0] for row in input]

def get_edges(input):
    edges = []
    for row in input:
        for y in row[1]:
            edges.append((row[0], y))
    return edges
    
edges = get_edges(input)

node_colors = [row[2] for row in input]

G = nx.Graph()
G.add_nodes_from(nodes)
G.add_edges_from(edges)

nx.draw(G, node_color=node_colors, with_labels=True)
plt.savefig("graph.png")
