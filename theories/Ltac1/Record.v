(* Needed to deal with the 'abstract' tactic. See inline_private_constants.ml *)
Definition private_constant_placeholder (x : Type) := x.
Register private_constant_placeholder as tactician.private_constant_placeholder.

Declare ML Module "ltacX_common_plugin:coq-core.plugins.ltacX_common".
Declare ML Module "ltac_plugin:coq-core.plugins.ltac".
Declare ML Module "firstorder_plugin:coq-core.plugins.firstorder".
Declare ML Module "extraction_plugin:coq-core.plugins.extraction".
Declare ML Module "funind_plugin:coq-core.plugins.funind".
Declare ML Module "tactician_ltac1_record_plugin:coq-tactician.record-plugin".
#[export] Set Default Proof Mode "Tactician Ltac1".

Tactician Record Then Decompose.
Tactician Record Dispatch Decompose.
Tactician Record Extend Decompose.
Tactician Record Thens Decompose.
Tactician Record Thens3parts Decompose.
Tactician Record First Keep.
Tactician Record Solve Keep.
Tactician Record Or Keep.
Tactician Record Once Keep.
Tactician Record ExactlyOnce Keep.
Tactician Record IfThenCatch Keep.
Tactician Record Orelse Keep.
Tactician Record Do Keep.
Tactician Record Timeout Keep.
Tactician Record Repeat Keep.
Tactician Record Progress Keep.

(*
 The abstract tactic is a difficult beast to deal with for several reasons:
 a) It does not add proving power (it is only useful for advanced things, way beyond Tactician).
    However, we cannot decompose it, because the inner tactic of abstract is executed in a different context
    and therefore not recorded by Tactician. Hence, if we want to record something, this settings needs to
    remain "Keep".
 b) Abstract emits side-effects that need to either be inlined or otherwise dealt with in Tacticians recorded data.
    It is unclear what the best approach for this would be.
 c) The 'abstract' tactic is very error-prone, making Tactician crash. See https://github.com/coq/coq/issues/9146
    Note that setting this to 'Decompose' will not keep Tactician from using 'abstract' ever, because it could be
    part of a more complex expression (or inside of an ltac definition). This is better than nothing though.
 *)
Tactician Record Abstract Keep.
Tactician Record LetIn Keep.
Tactician Record Match Keep.
Tactician Record MatchGoal Keep.
Tactician Record Arg Keep.
Tactician Record Select Decompose. (* TODO: This setting should be kept like this until we implement
                                      an override in tactic_annotate in case we are in 'synth with cache' *)
Tactician Record ML Keep.
Tactician Record Alias Keep.
Tactician Record Call Keep.
Tactician Record IntroPattern Keep.
Tactician Record Apply Keep.
Tactician Record Elim Keep.
Tactician Record Case Keep.
Tactician Record MutualFix Keep.
Tactician Record MutualCofix Keep.
Tactician Record Assert Keep.
Tactician Record Generalize Keep.
Tactician Record LetTac Keep.
Tactician Record InductionDestruct Keep.
Tactician Record Reduce Keep.
Tactician Record Change Keep.
Tactician Record Rewrite Keep.
Tactician Record RewriteMulti Keep.
Tactician Record Inversion Keep.
