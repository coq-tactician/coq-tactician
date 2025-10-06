"""Generate a bird-eye-view visualization of (part of) a dataset with
Graphviz."""

import graphviz
from pytact.data_reader import lowlevel_data_reader
import sys
import json
from pathlib import Path
from collections import Counter
import cmath
import colorsys
import math

def get_node_id(gid, nid):
    prefix = f"{gid}-{nid}"
    return prefix

def init_graph():
    g = graphviz.Graph(engine='sfdp')
    g.attr('node', shape='point', width='0.01', height='0.01')
    g.attr('edge', color="#0000ff10")
    g.attr(overlap='prism', outputorder='edgesfirst')
    g.attr(ratio='fill', size="20,10")
    g.attr(bgcolor="transparent")
    return g

def make_color(n, alpha):
    rgb = colorsys.hsv_to_rgb(n+(1/2), 1, 1)
    hexrgb = ["%0.2X"%int(v * 255) for v in list(rgb)+[alpha]]
    return f"#{hexrgb[0]}{hexrgb[1]}{hexrgb[2]}{hexrgb[3]}"

def tooltip(n):
    if n.label.is_definition:
        return n.label.definition.name
    else:
        return n.label.which.name

def main():
    with lowlevel_data_reader(Path(sys.argv[1])) as data:

        subset = { p: gid for p, gid in data.graphid_by_filename.items()
                if Path('coq-tactician-stdlib.8.11.dev/theories/Init/') in p.parents }

        # subset = { p: gid for p, gid in data.graphid_by_filename.items()
        #            if Path('coq-tactician-stdlib.8.11.dev/theories/Init/Logic.bin') == p }

        print('Calculating node incoming count')
        incoming = Counter()
        for p, gid in subset.items():
            d = data[gid]
            for i, n in enumerate(d.graph.nodes):
                for ci in range(n.children_index, n.children_index + n.children_count):
                    target = d.graph.edges[ci].target
                    target_graph = data.local_to_global(gid, target.dep_index)
                    targetid = get_node_id(target_graph, target.node_index)
                    incoming[targetid] += 1
        incoming_max = incoming.most_common(1)[0][1]

        print('Calculating node positions')
        g = init_graph()
        for p, gid in subset.items():
            d = data[gid]
            for i, n in enumerate(d.graph.nodes):
                sourceid = get_node_id(gid, i)
                g.node(sourceid, width=str(0.001*incoming[sourceid]), height=str(0.001*incoming[sourceid]))
                for ci in range(n.children_index, n.children_index + n.children_count):
                    target = d.graph.edges[ci].target
                    target_graph = data.local_to_global(gid, target.dep_index)
                    targetid = get_node_id(target_graph, target.node_index)
                    g.edge(sourceid, targetid)
                    # print(f"{sourceid},{targetid}")
        g.render(filename='web', format='json', view=False, cleanup=False)

        print('Reading node positions')
        positions = dict()
        with open('web.json') as f:
            jsongraph = json.load(f)
            for node in jsongraph['objects']:
                position = node['pos'].split(',')
                position = complex(float(position[0]), float(position[1]))
                positions[node['name']] = position

        print('Calculating largest distance')
        maxdist = 0
        for p, gid in subset.items():
            d = data[gid]
            for i, n in enumerate(d.graph.nodes):
                sourceid = get_node_id(gid, i)
                for ci in range(n.children_index, n.children_index + n.children_count):
                    target = d.graph.edges[ci].target
                    target_graph = data.local_to_global(gid, target.dep_index)
                    targetid = get_node_id(target_graph, target.node_index)
                    maxdist = max(maxdist, abs(positions[sourceid]-positions[targetid]))
        print(f'Max distance: {maxdist}')

        print('Drawing final graph')
        g = init_graph()
        for p, gid in subset.items():
            d = data[gid]
            # print(p)
            for i, n in enumerate(d.graph.nodes):
                sourceid = get_node_id(gid, i)
                g.node(sourceid, width=str(0.001*incoming[sourceid]), height=str(0.001*incoming[sourceid]),
                    color=make_color((1/2)+(math.log(incoming[sourceid]+1)/math.log(incoming_max+1)), 1),
                    tooltip=tooltip(n))
                for ci in range(n.children_index, n.children_index + n.children_count):
                    target = d.graph.edges[ci].target
                    target_graph = data.local_to_global(gid, target.dep_index)
                    targetid = get_node_id(target_graph, target.node_index)
                    distance = abs(positions[sourceid]-positions[targetid])
                    distance_norm = distance / maxdist * 2
                    g.edge(sourceid, targetid, color=make_color(distance_norm, 0.2))
                    # print(f"{sourceid},{targetid}")
        g.render(filename='web', format='svg', view=False, cleanup=False)

# with data_reader(Path(sys.argv[1])) as data:

#     g = graphviz.Graph(engine='sfdp')
#     g.attr('node', shape='point', width='.1', height='.1')
#     g.attr('edge', penwidth="0.1")
#     g.attr(overlap='false')

#     # print("source,target")

#     for p, f in data.items():
#         if Path('coq-tactician-stdlib.dev/theories/Init/') not in p.parents:
#             continue
#         for d in f:
#             print(d.name)


#     # g.render(filename='web', view=False, cleanup=False)

if __name__ == "__main__":
    exit(main())
