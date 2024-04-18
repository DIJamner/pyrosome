(#"blk_subst"
    (#"cmp"
        (#"exch" "G" "H")
        (#"csub h g")
    (#"jmp" "b" "a")))

(#"blk_subst"
    (#"exch" "G" "H")
    (#"blk_subst"
        (#"csub h g")
        (#"jmp" "b" "a")))

(#"blk_subst"
    (#"exch" "G" "H")
    (#"jmp"
        (#"val_subst" "h" "b")
        (#"val_subst" "g" "a")))