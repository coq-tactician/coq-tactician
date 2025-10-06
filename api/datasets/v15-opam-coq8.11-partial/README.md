Tactician's Web of Large-Scale Formal Knowledge
================================================================================

This dataset contains machine-readable data extracted by [Tactician][1] from
formal knowledge encoded in the [Coq Proof Assistant][2]. It includes
definitions, theorems, proof terms and tactical proofs presented both as Coq's
default textual format and a graph format. The entire known universe of formal
knowledge in Coq is encoded as a single interconnected graph of mathematical
concepts where all knowledge is faithfully and unambiguously encoded. The
dataset is intended for machine learning, analysis and general proof engineering
purposes. In addition to exploring this offline dataset, it is also possible to
interact directly with Coq in the same data format through [Tactician's API][3].

[1]: https://coq-tactician.github.io
[2]: https://coq.inria.fr
[3]: https://coq-tactician.github.io/api


Accessing the data
--------------------------------------------------------------------------------

The data is encoded using the [Cap'n Proto serialization protocol][4], allowing
for fast random access to the graph and metadata from many programming
languages. The schema and documentation for the data can be found in
`meta/graph_api.capnp`. For each Coq compilation unit `X`, we include the
original `X.v` source file. Alongside that file is a `X.bin` file with Cap'n
Proto structure containing the data extracted during the compilation of `X`.

[4]: https://capnproto.org

For Python, a library called [PyTactician][5] is provided that allows for easy
and efficient access to the data. It includes software to visualize the dataset,
a sanity checker for the dataset, an example prediction server that interfaces
with Coq, an Oracle prediction server and an example proof exploration client.
This library is a good starting point to explore the dataset.

[5]: https://pypi.org/project/pytactician

The data in this archive is represented as a [SquashFS][6] image `dataset.squ`.
If you are using PyTactician, you can load the dataset by pointing
directly to this image. This will automatically mount the image in directory
`dataset/`. For example:

    pytact-check dataset.squ
    pytact-visualize dataset.squ

In order to make this work, [squashfuse][7] needs to be installed through your
favorite package manager. If you prefer to mount manually, or if you are not
using the PyTactician library, you can mount the image using

    squashfuse dataset.squ dataset/
    pytact-check dataset/
    pytact-visualize dataset/

If you have root access, you can mount the image more efficiently through

    mount dataset.squ dataset/

Finally, you can also unpack the image without mounting it. However, on systems
with limited memory or slow hard-disks this will lead to performance
degradations while accessing the dataset. Experiments show that due to the high
decompression speed of the image's LZ4 compression algorithm, mounting is almost
always preferrable to unpacking. Nevertheless, if you wish to unpack, you can
run:

    unsquashfs -dest dataset/ dataset.squ

If you wish to inspect the raw data in the dataset manually, you can use [capnp
convert][8] to decode an individual file in the dataset to JSON as follows:

    cat dataset/coq-tactician-stdlib.8.11.dev/theories/Init/Logic.bin | \
        capnp convert binary:json meta/graph_api.capnp Dataset

You can process the resulting JSON further using, for example, the `jq` command.

[6]: https://docs.kernel.org/filesystems/squashfs.html
[7]: https://github.com/vasi/squashfuse
[8]: https://capnproto.org/capnp-tool.html


Dataset contents
--------------------------------------------------------------------------------

This dataset is comprised of a collection of Coq packages curated through the
[Coq Package Index][9]. Because the data forms a single, consistent,
interconnected graph, a set of mutually co-installable packages needs to be
selected. The [Opam][10] package manager with the [aspcud][11] dependency solver
was used to compute the largest co-installable set. Details on these packages
are provided below. Note, however, that due to various outstanding bugs in Coq
and Tactician not all packages could be fully compiled:

- coq-metacoq-erasure.1.0~beta2+8.11 partial
- coq-coqtail.8.14 partial
- coq-mathcomp-odd-order.1.14.0 partial
- coq-qcert.2.2.0 partial
- coq-color.1.8.2 partial
- coq-coquelicot.3.2.0 partial
- coq-vst.2.6 partial
- coq-atbr.8.11.0 partial
- coq-corn.8.16.0 partial
- coq-metacoq.1.0~beta2+8.11 missing due to failure of dependency
- coq-interval.4.6.1 missing due to failure of dependency
- coq-pi-agm.1.2.5 missing due to failure of dependency

The files `meta/stage*.sh` contain the precise Opam commands that were used to
generate this dataset. Files `meta/opam-stage*` contain the precise state of the
Opam switch after each stage.

[9]: https://coq.inria.fr/packages.html
[10]: https://opam.ocaml.org
[11]: https://potassco.org/aspcud


### Overview of Coq packages in the dataset
