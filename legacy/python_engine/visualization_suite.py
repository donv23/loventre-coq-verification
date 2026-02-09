import plotly.graph_objects as go
import networkx as nx
import numpy as np
from typing import Dict

class TheoremVisualizer:
    def visualize_3d_space(self):
        x = np.linspace(-3, 3, 50)
        y = np.linspace(-3, 3, 50)
        X, Y = np.meshgrid(x, y)
        Z = np.sin(np.sqrt(X**2 + Y**2))
        
        fig = go.Figure(data=[go.Surface(z=Z, x=X, y=Y)])
        fig.update_layout(title="Spazio Metrico Loventre 3D")
        return fig
    
    def create_dependency_graph(self, dependencies: Dict):
        G = nx.DiGraph()
        
        for node, deps in dependencies.items():
            G.add_node(node)
            for dep in deps:
                G.add_edge(dep, node)
        
        return G
