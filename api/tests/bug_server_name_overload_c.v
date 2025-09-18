Load NNLearner.
Set Tactician Neural Server "127.0.0.1:33333".
From Tactician Require Import Ltac1.
Inductive True : Prop :=
  I : True.
Section T.
Variable A B : Prop.
Theorem proj1 : A /\ B -> A.
Proof. synth.
Qed.
(*
(env) [lasse@lasse-work tmp-model]$ g2t-server --tcp --model weights/checkpoint__epoch58/
2022-05-11 16:10:08.334168: W tensorflow/stream_executor/platform/default/dso_loader.cc:64] Could not load dynamic library 'libcudart.so.11.0'; dlerror: libcudart.so.11.0: cannot open shared object file: No such file or directory
2022-05-11 16:10:08.334187: I tensorflow/stream_executor/cuda/cudart_stub.cc:29] Ignore above cudart dlerror if you do not have a GPU set up on your machine.
2022-05-11 16:10:11.350490: W tensorflow/stream_executor/platform/default/dso_loader.cc:64] Could not load dynamic library 'libcuda.so.1'; dlerror: libcuda.so.1: cannot open shared object file: No such file or directory
2022-05-11 16:10:11.350511: W tensorflow/stream_executor/cuda/cuda_driver.cc:269] failed call to cuInit: UNKNOWN ERROR (303)
2022-05-11 16:10:11.350522: I tensorflow/stream_executor/cuda/cuda_diagnostics.cc:156] kernel driver does not appear to be running on this host (lasse-work): /proc/driver/nvidia/version does not exist
2022-05-11 16:10:11.350626: I tensorflow/core/platform/cpu_feature_guard.cc:151] This TensorFlow binary is optimized with oneAPI Deep Neural Network Library (oneDNN) to use the following CPU instructions in performance-critical operations:  AVX2 AVX512F FMA
To enable them in other operations, rebuild TensorFlow with the appropriate compiler flags.
PYTHON:  starting tcp/ip server on port 33333
PYTHON:  tcp/ip server is listening on 33333
PYTHON:  coq client connected  ('127.0.0.1', 44284)
PYTHON:  using RAM /run/user/1000 for internal message exchanges
PYTHON:  message:  synchronize
PYTHON:  (synchronize = 772303431)
PYTHON:  sending synchronize response in the initialize loop (synchronized = 772303431)
PYTHON:  message:  initialize
PYTHON:  ### CONTEXT 0 ####
PYTHON:  DUMP msg to  /run/user/1000/msg_init.0.bin
LOADING | c_load_init runs on /run/user/1000/msg_init.0.bin
LOADING | received tactic_index_to_hash table of size 995
LOADING | received node_class_to_hash table of size 17513
LOADING | in load_init_msg
LOADING | evaluation clib received definition names
LOADING | current hash_to_node size 17513
LOADING | inserting new definition with hash 657063909 with name Top.True_rec
LOADING | inserting new definition with hash 657060832 with name Top.True_ind
LOADING | inserting new definition with hash 346954063 with name Top.True_sind
LOADING | inserting new definition with hash 346945567 with name Top.True_rect
LOADING | inserting new definition with hash 84516510 with name Top.True
LOADING | inserting new definition with hash 919649162 with name Top.I
LOADING | again, def_table hash_to_node size 17519
LOADING | subgraphs nodes: 2501
LOADING | populated visible context of size 803
PYTHON:  initialize tactics []
PYTHON:  initialize definitions [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
PYTHON:  sending initialize response (initialized = void)
PYTHON:  message:  predict
PYTHON:  DUMP msg to  /run/user/1000/msg_predict.0.1.bin
LOADING | in load_msg
LOADING | subgraphs nodes: 2501
LOADING | received context of length 0
LOADING | exception in load_msg
LOADING | _Map_base::at
Traceback (most recent call last):
  File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/bin/g2t-server", line 33, in <module>
    sys.exit(load_entry_point('graph2tac', 'console_scripts', 'g2t-server')())
  File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/pserver.py", line 225, in main
    main_loop(reader, sock, predict)
  File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/pserver.py", line 137, in main_loop
    raw_state = load_msg(c_data, os.fsencode(fname), theorem_state_cnt, bfs_option, max_subgraph_size)
TypeError: _Map_base::at
LOADING | c_data destructor is called: freeing memory
LOADING | c_data destruction complete
*)