module type DATA = sig
    type feature
    type features
    type 'a example = features * ('a option)
    type 'a examples = 'a example list
    type direction = Left | Right
    type rule = features -> direction
    val rule_of_fea : feature -> rule
    val is_empty : 'a examples -> bool
    val add : 'a examples -> 'a example -> 'a examples
    val features : 'a example -> features
    val split : feature -> 'a examples -> 'a examples * 'a examples
    val gini_rule : 'a examples -> feature
    val random_label : 'a examples -> 'a
    val random_example : 'a examples -> 'a example
    val fold_left : ('a -> 'b example -> 'a) -> 'a -> 'b examples -> 'a
    val label : 'a example -> 'a
    val labels : 'a examples -> 'a list
end

module Make = functor (Data : DATA) -> struct

    type 'a tree =
        | Node of Data.feature * ('a tree) * ('a tree)
        | Leaf of 'a * ('a Data.examples)

    let leaf example =
        Leaf (Data.label example, [example])

    (* returns Node(split_rule, Leaf (label1, stats1), Leaf(label2, stats2)) *)
    let make_new_node examples =
        let rule = Data.gini_rule examples in
        let examples_l, examples_r = Data.split rule examples in
        if Data.is_empty examples_l || Data.is_empty examples_r
        then Leaf(Data.random_label examples, examples)
        else Node(rule,
            Leaf(Data.random_label examples_l, examples_l),
            Leaf(Data.random_label examples_r, examples_r))

    let init_cond ?(min_impur=0.5) examples =
        let labels = Data.labels examples in
        let impur = Impurity.gini_impur labels in
        impur > min_impur

    (* pass the example to a leaf; if a condition is satisfied, extend the tree *)
    let add ?(min_impur=0.5) tree example =
        let rec loop = function
            | Node (fea, tree_l, tree_r) ->
                (match (Data.rule_of_fea fea) (Data.features example) with
                | Left  -> Node(fea, loop tree_l, tree_r)
                | Right -> Node(fea, tree_l, loop tree_r))
            | Leaf (label, examples) ->
                let examples = Data.add examples example in
                if init_cond ~min_impur examples then make_new_node examples
                else Leaf (label, examples)
        in
        loop tree

    let tree examples =
        let example = Data.random_example examples in
        Data.fold_left add (leaf example) examples

    let classify example tree =
        let rec loop tree =
            match tree with
            | Leaf (cls, _) -> cls
            | Node (fea, tree_l, tree_r) ->
                (match (Data.rule_of_fea fea) (Data.features example) with
                | Left  -> loop tree_l
                | Right -> loop tree_r)
        in loop tree

    let depth tree =
        let rec loop d t =
            match t with
            | Node(_, tl, tr) -> max (loop (d+1) tl) (loop (d+1) tr)
            | Leaf(_) -> d
        in loop 0 tree

    let n_nodes tree =
        let rec loop t =
            match t with
            | Node(_, tl, tr) -> 1 + (loop tl) + (loop tr)
            | Leaf(_) -> 1
        in loop tree

    let max_node tree =
        let rec loop t =
            match t with
            | Node(_, tl, tr) -> max (loop tl) (loop tr)
            | Leaf(_, es) -> List.length es
        in loop tree

    let max_labels_node tree =
        let rec loop t =
            match t with
            | Node(_, tl, tr) -> max (loop tl) (loop tr)
            | Leaf(_, es) -> List.length (Utils.uniq (Data.labels es))
        in loop tree

end
