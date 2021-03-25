module type DATA = sig
    type features
    type 'a example = features * ('a option)
    type 'a examples = 'a example list
    type direction = Left | Right
    type rule = features -> direction
    val is_empty : 'a examples -> bool
    val add : 'a examples -> 'a example -> 'a examples
    val features : 'a example -> features
    val split : rule -> 'a examples -> 'a examples * 'a examples
    val gini_rule : 'a examples -> rule
    val random_label : 'a examples -> 'a
    val random_example : 'a examples -> 'a example
    val fold_left : ('a -> 'b example -> 'a) -> 'a -> 'b examples -> 'a
    val label : 'a example -> 'a
    val labels : 'a examples -> 'a list
end

module Make = functor (Data : DATA) -> struct

    type 'a tree =
        | Node of Data.rule * ('a tree) * ('a tree)
        | Leaf of 'a * ('a Data.examples)

    let leaf example =
        Leaf (Data.label example, [example])

    (* returns Node(split_rule, Leaf (label1, stats1), Leaf(label2, stats2)) *)
    let make_new_node examples =
(*         let () = Printf.printf "make_new_node\n" in *)
        let rule = Data.gini_rule examples in
        let examples_l, examples_r = Data.split rule examples in
        if Data.is_empty examples_l || Data.is_empty examples_r
        then Leaf(Data.random_label examples, examples)
        else Node(rule,
            Leaf(Data.random_label examples_l, examples_l),
            Leaf(Data.random_label examples_r, examples_r))

    let prelim_conds examples depth =
        let labels = Data.labels examples in
        let imp = Impurity.gini_impur labels in
        depth < 100 && imp > 0.3
    (* TODO more sophisticated condition needed *)

    (* pass the example to a leaf; if a condition is satisfied, extend the tree *)
    let add tree example =
        let rec loop depth = function
            | Node (rule, tree_l, tree_r) ->
                (match rule (Data.features example) with
                | Left  -> let subtree, correct = loop (depth + 1) tree_l in
                        (Node(rule, subtree, tree_r), correct)
                | Right  -> let subtree, correct = loop (depth + 1) tree_r in
                        (Node(rule, subtree, tree_l), correct))
            | Leaf (label, examples) ->
                let correct = label = Data.label example in
                let examples = Data.add examples example in
                let subtree =
                    if prelim_conds examples depth then make_new_node examples
                    else Leaf (label, examples) in
                (subtree, correct)
        in
        loop 0 tree

    let classify example tree =
        let rec loop tree =
            match tree with
            | Leaf (cls, _) -> cls
            | Node (rule, tree_l, tree_r) ->
                (match rule (Data.features example) with
                | Left  -> loop tree_l
                | Right -> loop tree_r)
        in loop tree

    let depth tree =
        let rec loop d t =
            match t with
            | Node(_, tl, tr) -> max (loop (d+1) tl) (loop (d+1) tr)
            | Leaf(_) -> d
        in loop 0 tree

    let max_node tree =
        let rec loop t =
            match t with
            | Node(_, tl, tr) -> max (loop tl) (loop tr)
            | Leaf(_, es) -> List.length es
        in loop tree

end
