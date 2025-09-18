"""# PyTactician

This is the API documentation of the PyTactician library that assists in
interfacing with Tactician's API to the Coq proof assistant from Python. The
main entry-point for the API is `pytact.data_reader`, which contains functions
for loading and exploring dataset as well as abstractions around the
communication protocol with Coq.

PyTactician also provides several command-line programs such as a dataset
sanity checker, a visualization webserver, and several proving servers. Their
implementations may be instructive examples on the usage of `pytact.data_reader`.
Implementations for each program can be found here:

- `pytact-server`: `pytact.fake_python_server` is a minimal example for a proving server
- `pytact-oracle`: `pytact.oracle_server` is a good example both of a proving server
  and getting data from a dataset
- `pytact-visualize`: `pytact.graph_visualize_browse` for the visualization logic
  and `pytact.visualisation_webserver` for the server
- `pytact-check`: `pytact.graph_sanity_check` (mostly low-level access to the
  dataset, not idiomatic high-level code)

In addition to these programs, there are some code snippets in `pytact.scripts`
that may be instructive.

"""
