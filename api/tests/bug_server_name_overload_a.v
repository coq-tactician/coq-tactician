Load NNLearner.
Set Tactician Neural Server "127.0.0.1:33333".
From Tactician Require Import Ltac1.

Definition True := Coq.Init.Logic.True.
Goal True.
synth. (* Crashes in a blaze of glory *)
Qed.

(*
(env) [lasse@lasse-work tmp-model]$ g2t-server --tcp --model weights/checkpoint__epoch58/
2022-05-11 15:56:32.840045: W tensorflow/stream_executor/platform/default/dso_loader.cc:64] Could not load dynamic library 'libcudart.so.11.0'; dlerror: libcudart.so.11.0: cannot open shared object file: No such file or directory
2022-05-11 15:56:32.840064: I tensorflow/stream_executor/cuda/cudart_stub.cc:29] Ignore above cudart dlerror if you do not have a GPU set up on your machine.
2022-05-11 15:56:35.899683: W tensorflow/stream_executor/platform/default/dso_loader.cc:64] Could not load dynamic library 'libcuda.so.1'; dlerror: libcuda.so.1: cannot open shared object file: No such file or directory
2022-05-11 15:56:35.899703: W tensorflow/stream_executor/cuda/cuda_driver.cc:269] failed call to cuInit: UNKNOWN ERROR (303)
2022-05-11 15:56:35.899713: I tensorflow/stream_executor/cuda/cuda_diagnostics.cc:156] kernel driver does not appear to be running on this host (lasse-work): /proc/driver/nvidia/version does not exist
2022-05-11 15:56:35.899848: I tensorflow/core/platform/cpu_feature_guard.cc:151] This TensorFlow binary is optimized with oneAPI Deep Neural Network Library (oneDNN) to use the following CPU instructions in performance-critical operations:  AVX2 AVX512F FMA
To enable them in other operations, rebuild TensorFlow with the appropriate compiler flags.
PYTHON:  starting tcp/ip server on port 33333
PYTHON:  tcp/ip server is listening on 33333
PYTHON:  coq client connected  ('127.0.0.1', 44276)
PYTHON:  using RAM /run/user/1000 for internal message exchanges
PYTHON:  message:  synchronize
PYTHON:  (synchronize = 295300214)
PYTHON:  sending synchronize response in the initialize loop (synchronized = 295300214)
PYTHON:  message:  initialize
PYTHON:  ### CONTEXT 0 ####
PYTHON:  DUMP msg to  /run/user/1000/msg_init.0.bin
LOADING | c_load_init runs on /run/user/1000/msg_init.0.bin
LOADING | received tactic_index_to_hash table of size 995
LOADING | received node_class_to_hash table of size 17513
LOADING | in load_init_msg
LOADING | evaluation clib received definition names
LOADING | current hash_to_node size 17513
LOADING | inserting new definition with hash 436303052 with name Top.True
LOADING | again, def_table hash_to_node size 17514
LOADING | subgraphs nodes: 2492
LOADING | populated visible context of size 798
PYTHON:  initialize tactics []
PYTHON:  initialize definitions [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
PYTHON:  sending initialize response (initialized = void)
PYTHON:  message:  predict
PYTHON:  DUMP msg to  /run/user/1000/msg_predict.0.1.bin
LOADING | in load_msg
LOADING | subgraphs nodes: 2492
LOADING | received context of length 0
PYTHON:  received context of length 0
PYTHON:  visible context: [17340 17239 17218 17154 17124 17094 16980 16966 16962 16924 16857 16856
 16855 16747 16746 16733 16698 16636 16635 16560 16398 16397 16372 16371
 16346 16105 16029 16018 16017 15993 15905 15890 15775 15774 15772 15770
 15691 15626 15502 15427 15425 15420 15403 15397 15263 15227 15215 15214
 15167 14970 14969 14901 14836 14814 14810 14731 14710 14709 14708 14552
 14551 14476 14359 14305 14304 14303 14198 14170 14133 14036 13955 13882
 13881 13862 13836 13777 13694 13592 13591 13574 13566 13408 13391 13390
 13389 13388 13381 13380 13325 13324 13313 13283 13282 13218 13211 13141
 13139 13111 13079 13078 13062 13059 12932 12877 12876 12781 12756 12752
 12751 12659 12639 12550 12534 12510 12501 12417 12416 12414 12413 12094
 12089 12060 12059 11992 11990 11972 11881 11880 11763 11625 11624 11472
 11418 11417 11365 11359 11358 11357 11332 11331 11291 11286 11285 11284
 11239 11221 11172 11097 10909 10866 10865 10863 10803 10732 10689 10685
 10662 10530 10529 10462 10449 10448 10446 10382 10311 10310 10309 10308
 10285 10143 10141 10093 10066 10026 10025  9995  9990  9989  9988  9957
  9939  9937  9902  9901  9870  9869  9867  9767  9741  9736  9721  9702
  9694  9693  9568  9566  9485  9415  9414  9411  9407  9400  9395  9315
  9308  9307  9291  9277  9276  9272  9271  9263  9260  9183  9158  9157
  9151  9131  9124  9123  9122  9121  9069  9068  9055  9054  9046  9045
  9044  9043  8926  8914  8907  8861  8846  8808  8788  8774  8773  8764
  8756  8724  8683  8682  8672  8671  8616  8572  8553  8552  8440  8439
  8415  8395  8380  8363  8338  7944  7924  7887  7882  7825  7824  7811
  7748  7746  7633  7589  7459  7457  7365  7361  7288  7276 17484  7179
  7176  7052  7050  6999  6974  6948  6875  6762  6626  6595  6470  6450
  6449  6329  6213  6095  6092  6014  6012  5876  5693  5600  5555  5542
  5526  5500  5489  5410  5355  5354  5325  5324  5249  5248  5124  5091
  5090  5046  5045  5019  5018  5012  4979  4978  4962  4960  4900  4899
  4792  4791  4738  4731  4730  4729  4728  4509  4484  4453  4443  4442
  4424  4410  4405  4384  4322  4268  4255  4221  4217  4215  4204  4203
  4202  4201  4200  4199  4183  4162  4127  4126  4114  4113  4094  4073
  4072  4017  3993  3990  3932  3931  3799  3710  3538  3528  3526  3525
  3524  3522  3521  3520  3519  3517  3516  3505  3504  3503  3502  3501
  3500  3499  3498  3497  3496  3495  3494  3493  3492  3491  3490  3466
  3205  3204  2994  2993  2896  2872  2871  2852  2851  2669  2588  2480
  2479  2469  2454  2381  2380  2356  2355  2354  2305  2304  2303  2037
  2036  2034  1753  1752  1751  1671  1669  1668  1605  1514  1513  1386
  1385  1383  1376  1207  1206  1205   960   936   832   799   678   543
   407   394   376   375   178  7731  9787  2654  8659 14782 12592  9729
  1355 12312  5348 10316  8690 11870 11392  1915 12947  1870 13229  1882
 14011 14385 13870   821  5413  5076   193  2664 13382 15417 11441 13375
  1902  5437  4916  9285 12615  4258 16768 16408  1868 11104 17201 16278
 13594  3813  1784  1061  5746 15745 11280  6534  8492  9427 16193  5360
  7268 14801   134 15402 15235 10030  1273  7899  5496  1990  4209 14821
 15645 14057  2674 11507 12183  4597 16122   677 17223  3289  9180  4414
  3281 10914 13046 14085  9735 11421 13351  7445 15911   944  9532 10983
 11922   809  5567  7611 12922 11273  1881  3898 12551  8253  6720  8047
 12521 13681  4386 15157  8657  3688  8991 15675 11954  3046 10745  4966
  3718 15299  9753  6998 14781  9602 14323  9789 10919   707 13543  1738
 13876  6884  6565  2106  3527  6566  1164  1243 15657 10269  2185 13146
  8642 14646 15071  9875  3061  5895 10054  9955  2842  9224  8347  9493
  4951  8194  5834   484  7453 12941 10503 16699   867 11908  7058   882
  8406 15779  8660 11575 11679 15920 13163  9216  3436 10486  6340 10950
  5292 14310  2863  7336  3119  3428   698  8285 12228 12428 16861  6457
 14131 14102  7070 15546  1310 12272  1793   681 17441  4933 11662  2544
  6423  5009  7119 11785  2671  6530 16862  9856 11492 11406  7636 13273
  9714  3751   514 17345 11063 11527 10458   275 10165 10541 10297  5816
 13205  2775  9634  4077  6435 16369  2832  8445 13863  9362 10088  9695
    21 13172  2085  2310 10667 17136 17093 12181  1231 12116  1631 16203
  3206  1924 12913  4483  7257  7768  6810  1161  3431 14879  9461  4803
 12216 11249 16250  6555  5418  4020  4848  5476  6480 10941  9793 14696
 11087 15520  1342 15374 11004 10985  3787 12460  8822  5287 16513  9504
  8049   822  8094 14891  5195  1724   384 11289  4733 16005 15486  2766
 14615 10959 14155  7773  1040 15876  7534 17020 16424 10790  4071  9160
 16584  1992 13717  6513 12988  5159 15564 12067  7923 13130 12031 15603
  4810 11612 14733 14313 14692  4095  3410 15542  8452  6200  9886  6040
 16153 13311 12939  9971  4582  7788 15320  1384  5777 15072  1637 14144
 11476 11250 14565 10870 15545  9324]
Warning: ignoring new definitions!
Traceback (most recent call last):
  File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/bin/g2t-server", line 33, in <module>
    sys.exit(load_entry_point('graph2tac', 'console_scripts', 'g2t-server')())
  File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/pserver.py", line 225, in main
    main_loop(reader, sock, predict)
  File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/pserver.py", line 139, in main_loop
    process_predict(sock, msg, raw_state,  predict, c_data, theorem_state_cnt,  tacs, tac_numargs, tactic_hash_to_index)
  File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/pserver.py", line 94, in process_predict
    actions, confidences = predict.ranked_predictions(state, allowed_model_tactics, available_global = visible_context, tactic_expand_bound=8, total_expand_bound=64)
  File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/predict.py", line 114, in ranked_predictions
    top_tactic_ids, tactic_logits, arg_nums, arg_logits = self.predict_tactic_arg_logits(state, tactic_expand_bound, allowed_model_tactics, available_global)
  File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/predict.py", line 85, in predict_tactic_arg_logits
    tactic_logits = self.predict_tactic_logits(state)
  File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/predict.py", line 58, in predict_tactic_logits
    tactic_logits, _, _ = self.pred_fn(model_input)  # [bs, tactics], _, _
  File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/tensorflow/python/util/traceback_utils.py", line 153, in error_handler
    raise e.with_traceback(filtered_tb) from None
  File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/tensorflow/python/eager/execute.py", line 54, in quick_execute
    tensors = pywrap_tfe.TFE_Py_Execute(ctx._handle, device_name, op_name,
tensorflow.python.framework.errors_impl.InvalidArgumentError: Graph execution error:

Detected at node 'tactic_arg_training/initial_node_embedding/node_and_def_embedding/embedding/embedding_lookup' defined at (most recent call last):
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/bin/g2t-server", line 33, in <module>
      sys.exit(load_entry_point('graph2tac', 'console_scripts', 'g2t-server')())
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/pserver.py", line 225, in main
      main_loop(reader, sock, predict)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/pserver.py", line 139, in main_loop
      process_predict(sock, msg, raw_state,  predict, c_data, theorem_state_cnt,  tacs, tac_numargs, tactic_hash_to_index)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/pserver.py", line 94, in process_predict
      actions, confidences = predict.ranked_predictions(state, allowed_model_tactics, available_global = visible_context, tactic_expand_bound=8, total_expand_bound=64)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/predict.py", line 114, in ranked_predictions
      top_tactic_ids, tactic_logits, arg_nums, arg_logits = self.predict_tactic_arg_logits(state, tactic_expand_bound, allowed_model_tactics, available_global)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/predict.py", line 85, in predict_tactic_arg_logits
      tactic_logits = self.predict_tactic_logits(state)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/predict.py", line 58, in predict_tactic_logits
      tactic_logits, _, _ = self.pred_fn(model_input)  # [bs, tactics], _, _
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/model.py", line 757, in pred_fn
      return self.model(batch)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/keras/utils/traceback_utils.py", line 64, in error_handler
      return fn(*args, **kwargs)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/keras/engine/base_layer.py", line 1096, in __call__
      outputs = call_fn(inputs, *args, **kwargs)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/keras/utils/traceback_utils.py", line 92, in error_handler
      return fn(*args, **kwargs)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/keras/engine/functional.py", line 451, in call
      return self._run_internal_graph(
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/keras/engine/functional.py", line 589, in _run_internal_graph
      outputs = node.layer(*args, **kwargs)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/keras/utils/traceback_utils.py", line 64, in error_handler
      return fn(*args, **kwargs)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/keras/engine/base_layer.py", line 1096, in __call__
      outputs = call_fn(inputs, *args, **kwargs)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/keras/utils/traceback_utils.py", line 92, in error_handler
      return fn(*args, **kwargs)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/model.py", line 173, in call
      node_embs = self.node_and_def_embedding_layer(node_classes.values) # [total_nodes, dim]
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/keras/utils/traceback_utils.py", line 64, in error_handler
      return fn(*args, **kwargs)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/keras/engine/base_layer.py", line 1096, in __call__
      outputs = call_fn(inputs, *args, **kwargs)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/keras/utils/traceback_utils.py", line 92, in error_handler
      return fn(*args, **kwargs)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/graph2tac/tf2/model.py", line 152, in call
      emb = self._embedding_layer(ix)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/keras/utils/traceback_utils.py", line 64, in error_handler
      return fn(*args, **kwargs)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/keras/engine/base_layer.py", line 1096, in __call__
      outputs = call_fn(inputs, *args, **kwargs)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/keras/utils/traceback_utils.py", line 92, in error_handler
      return fn(*args, **kwargs)
    File "/home/lasse/Documents/Projects/Tactician/graph2tac/env/lib/python3.10/site-packages/keras/layers/embeddings.py", line 197, in call
      out = tf.nn.embedding_lookup(self.embeddings, inputs)
Node: 'tactic_arg_training/initial_node_embedding/node_and_def_embedding/embedding/embedding_lookup'
indices[1] = 17513 is not in [0, 17513)
	 [[{{node tactic_arg_training/initial_node_embedding/node_and_def_embedding/embedding/embedding_lookup}}]] [Op:__inference_pred_fn_24597]
LOADING | c_data destructor is called: freeing memory
LOADING | c_data destruction complete
*)