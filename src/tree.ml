open Printf

module type DATA = sig
    type indices = int list
    type examples
    type rule
    type label
    type split_rule = examples -> examples * examples
    val uniform_labels : examples -> bool
    val indices : examples -> indices
    val is_empty : examples -> bool
    val random_label : examples -> label
    val random_subset : examples -> examples
    val split : rule -> split_rule
end

module Make = functor (Data : DATA) -> struct

    type tree = Node of Data.split_rule * tree * tree | Leaf of Data.label

    let tree ?max_depth:(max_depth=10) rule examples =
        let rec loop examples depth =
            if Data.uniform_labels examples || depth = 0 then
                Leaf(Data.random_label examples)
            else
                let split = Data.split (rule examples) in
                let examples_l, examples_r = split examples in
                if Data.is_empty examples_l || Data.is_empty examples_r then
                    Leaf(Data.random_label examples)
                else
                    Node(split,
                        (loop examples_l (depth - 1)),
                        (loop examples_r (depth - 1)))
        in
        let tree = loop examples max_depth in
        tree

    let classify examples tree =
        let rec loop tree examples =
            match tree with
            | Leaf cls -> List.map (fun i -> (i, cls)) (Data.indices examples)
            | Node (split_rule, tree_l, tree_r) ->
                let examples_l, examples_r = split_rule examples in
                (loop tree_l examples_l) @
                (loop tree_r examples_r)
        in
        let inds_labels = loop tree examples in
        let inds = Data.indices examples in
        List.map (fun i -> List.assoc i inds_labels) inds
end
