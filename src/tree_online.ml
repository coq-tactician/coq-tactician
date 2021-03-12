module type DATA = sig
    type features
    type 'a example = features * ('a option)
    type 'a examples = 'a example list
    type rule = features -> bool
    type 'a split_rule = 'a examples -> 'a examples * 'a examples
    val uniform_labels : 'a examples -> bool
    val empty : 'a examples
    val is_empty : 'a examples -> bool
    val add : 'a examples -> 'a example -> 'a examples
    val unlabeled : features -> 'a example
    val random_label : 'a examples -> 'a
    val first_label : 'a examples -> 'a
    val random_subset : 'a examples -> 'a examples
    val split : rule -> 'a split_rule
    val gini_rule : ?m:int -> 'a examples -> rule
    val length : 'a examples -> int
    val random_example : 'a examples -> 'a example
    val fold_left : ('a -> 'a example -> 'a) -> 'a -> 'a examples -> 'a
    val label : 'a example -> 'a
    val labels : 'a examples -> 'a list
end

module Make = functor (Data : DATA) -> struct

    type 'a tree =
        | Node of 'a Data.split_rule * 'a tree * 'a tree
        | Leaf of 'a * 'a Data.examples

    let leaf example =
        Leaf (Data.label example, [example])

    (* returns Node(split_rule, Leaf (label1, stats1), Leaf(label2, stats2)) *)
    let make_new_node examples =
        let split_rule = Data.split (Data.gini_rule examples) in
        let examples_l, examples_r = split_rule examples in
        if Data.is_empty examples_l || Data.is_empty examples_r
        then Leaf(Data.random_label examples, examples)
        else
            Node(split_rule,
                Leaf(Data.random_label examples_l, examples_l),
                Leaf(Data.random_label examples_r, examples_r))

(*
    let extend examples =
        if Data.length examples > 10 then true else false
*)

    let extend examples =
        let labels = Data.labels examples in
        let imp = Impurity.gini_impur labels in
        imp > 0.5

    (* TODO more sophisticated condition needed *)

    (* pass the example to a leaf; if a condition is satisfied, extend the tree *)
    let add tree example =
        let rec loop = function
            | Node (split_rule, left_tree, right_tree) ->
(*                 let rule = Data.split_rev split_rule in *)
(*                 (match rule example with *)
                let examples_l, examples_r = split_rule [example] in
                (match Data.is_empty examples_l, Data.is_empty examples_r with
                | false, true -> Node(split_rule, loop left_tree, right_tree)
                | true, false  -> Node(split_rule, left_tree, loop right_tree)
                | _, _ -> failwith "single example goes either left or right")
            | Leaf (label, examples) ->
                let examples = Data.add examples example in
                if extend examples then make_new_node examples
                else Leaf (label, examples)
        in
        loop tree

    let tree examples =
        let example = Data.random_example examples in
        Data.fold_left add (leaf example) examples

    let classify examples tree =
        let rec loop tree examples =
            match tree with
            | Leaf (cls, _) ->
                List.map (fun e -> (e, cls)) examples
            | Node (split_rule, tree_l, tree_r) ->
                let examples_l, examples_r = split_rule examples in
                (loop tree_l examples_l) @
                (loop tree_r examples_r)
        in
        let examples_labels = loop tree examples in
        List.map (fun e -> List.assoc e examples_labels) examples
end

