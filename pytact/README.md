# PyTactician

PyTactician is a Python Library for interfacing with the [Coq Proof
Assistant](https://coq.inria.fr) through the
[API](https://coq-tactician.github.io/api) of its
[Tactician](https://coq-tactician.github.io) plugin and reading associated
datasets.

PyTactician is versioned as `x.y.z`. The major version number `x` indicates the
version of the dataset it is compatible with. The minor version number `y`
corresponds to the version of the communication protocol with Coq. Finally, `z`
is incremented when the API of PyTactician changes, without the schema of the
dataset or communication protocol changing.

## Installation

Binary wheels are provided for Linux and MacOS (on
[PyPI](https://pypi.org/project/pytactician)). On those platforms you can
install by executing `pip install pytactician`. If you need to install from
source, you need to have Cap'n Proto >= 0.8 installed on your system. See the
main repo
[README](https://github.com/coq-tactician/coq-tactician-api#prerequisites) for
more details on prerequisites. Once you have the prerequisites, you can install
by running `pip install .` from the root of the repository.

## Usage

PyTactician provides a library to work with the datasets extracted from Coq and
to directly interface with Coq through Tacticians API. The documentation for the
library can be found
[here](https://coq-tactician.github.io/api/pytactician-pdoc).

In addition, PyTactician contains a number of executables that can be used to
analyze datasets and interact with Coq. Available executables are as follows
(use the `--help` flag for each executable to learn about all the options).

- `pytact-check [-h] [--jobs JOBS] [--quick] [--verbose VERBOSE] dir`
   Run sanity checks on a dataset and print some statistics.
- `pytact-visualize [-h] [--port PORT] [--hostname HOSTNAME] [--dev] [--fast | --workers WORKERS] dataset`:
   Start an interactive server that visualizes a dataset.
- `pytact-server [-h] [--tcp TCP] [--record RECORD_FILE] {graph,text}`
  Example python server capable of communicating with Coq through Tactician's 'synth' tactic
  To learn how to interface Coq and Tactician with this server, see the sections below.
- `pytact-oracle [-h] [--tcp PORT] [--record RECORD_FILE] {graph,text} dataset`
  A tactic prediction server acting as an oracle, retrieving it's information from a dataset
- `pytact-fake-coq [-h] (--tcp TCP_LOCATION | --stdin EXECUTABLE) data`
  A fake Coq client that connects to a prediction server and feeds it a stream of previously recorded messages.
- `pytact-prover`: A dummy example client that interfaces with Coq and Tactician for proof exploration
  driven by the client.
