import inflection
import graphviz
from pytact.data_reader import ProofState, Node

# Load the cap'n proto library, and the communication specification in 'graph_api.capnp'
import capnp
import pytact.graph_api_capnp as graph_api_capnp

# TODO: Clean up and unify all the functions below

arrow_heads = [ "dot", "inv", "odot", "invdot", "invodot" ]
edge_arrow_map = {}
for group in graph_api_capnp.groupedEdges:
    count = 0
    for sort in group.conflatable:
        edge_arrow_map[sort] = arrow_heads[count]
        count += 1

edge_arrow_map2 = {e.raw : arrow for (e, arrow) in edge_arrow_map.items()}

def visualize_proof_state(state: ProofState):

    dot = graphviz.Digraph()
    dot.attr('graph', ordering="out")

    seen = set()
    nodes_left = 100

    def recurse(node: Node, depth):
        nonlocal seen
        nonlocal nodes_left

        id = str(node)
        if id in seen:
            return id
        seen.add(id)
        nodes_left -= 1
        if nodes_left < 0:
            id = 'trunc' + str(nodes_left)
            dot.node(id, 'truncated')
            return id

        if d := node.definition:
            label = d.name
        else:
            label = inflection.camelize(str(node.label.which.name.lower()))
        dot.node(id, label=label)
        if node.definition:
            depth -= 1
        if depth >= 0:
            for edge, child in node.children:
                cid = recurse(child, depth)
                dot.edge(id, cid, arrowtail=edge_arrow_map2[edge], dir="both")
        return id
    recurse(state.root, 0)

    dot.render(filename='python_graph', view=False, cleanup=True)

def visualize(graph, state, showLabel = False, graph1 = None,
              filename='python_graph', cleanup=True):
    nodes = graph.nodes
    root = state.root
    context = state.context
    assert all(n < len(nodes) for n in context)

    dot = graphviz.Digraph()
    dot.attr('graph', ordering="out")
    for node, value in enumerate(nodes):
        label = value.label.which()
        if node in context: label = str(node) + ': ['+label+']'
        if node == root:
            label = "Root: "+label
        dot.node(str(node), label)
    for node, value in enumerate(nodes):
        for edge in list(graph.edges)[value.childrenIndex:value.childrenIndex+value.childrenCount]:
            if graph1 != None and edge.target.depIndex == 1:
                target = '1#'+str(edge.target.nodeIndex)
                dot.node(target, "Global:"
                         + str(graph1.nodes[edge.target.nodeIndex].label.definition.name))
            else:
                target = str(edge.target.nodeIndex)
            if showLabel:
                label = str(edge.label)
            else:
                label = ""
            dot.edge(str(node), target, label=label,
                     arrowtail=edge_arrow_map[edge.label], dir="both")

    dot.render(filename=filename, view=False, cleanup=cleanup)

def visualize_defs(graph, defs, showLabel=False, filename='python_grapn', cleanup=True):
    nodes = graph.nodes
    assert all(n < len(nodes) for n in defs)
    dot = graphviz.Digraph()
    dot.attr('graph', ordering="out")
    for node, value in enumerate(nodes):
        label = value.label.which()
        if node in defs: label = str(node) + ': ' + value.label.definition.name
        dot.node(str(node), label)
    for node, value in enumerate(nodes):
        for edge in list(graph.edges)[value.childrenIndex:value.childrenIndex+value.childrenCount]:
            if showLabel:
                label = str(edge.label)
            else:
                label = ""
            dot.edge(str(node), str(edge.target.nodeIndex), label=label,
                     arrowtail=edge_arrow_map[edge.label], dir="both")

    dot.render(filename=filename, view=False, cleanup=True)

def visualize_exception(reason, filename='visualize_graph.pdf', cleanup=None):
    dot = graphviz.Digraph()
    dot.node(str(reason), str(reason))
    dot.render(filename, view=False, cleanup=cleanup)


class Visualizer:
    def __init__(self, filename, count, show_labels, cleanup):
        self.filename = filename
        self.cnt = 0
        self.count = count
        self.show_labels = show_labels
        self.cleanup = cleanup
    def _visualize(self, filename, result):
        if result.which() == 'newState':
            visualize(result.newState.graph, result.newState.state,
                         filename=filename, showLabel=self.show_labels, cleanup=self.cleanup)
        else:
            visualize_exception(result, filename=self.filename, cleanup=self.cleanup)

    def render(self, result):
        filename = self.filename
        if self.count:
            filename += str(self.cnt)
            self.cnt += 1

        self._visualize(filename, result)
