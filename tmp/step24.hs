(!! {{e #"blk_subst"
    (#"exch" "G" (ext "H" (#"neg" "B")))
    (#"blk_subst"
        (#"exch" (ext "H" (#"neg" "B")) "G")
        (#"blk_subst"
            (#"csub" (#"id" "G") (#"vsub" (#"pair" "v" (#"hd" (#"neg" "B")))))
            (#"pm_pair" (#"hd" (#"prod" "A" (#"neg" "B"))) "e")))}})