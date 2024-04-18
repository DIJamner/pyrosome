(!! {{e #"blk_subst"
    (#"exch" "G" (ext "H" (#"neg" "B")))
    (#"blk_subst"
        (#"exch" (ext "H" (#"neg" "B")) "G")
        (#"jmp"
            (#"val_subst"
                (#"vsub"
                    (#"cont"
                        (#"prod" "A" (#"neg" "B"))
                        (#"pm_pair" (#"hd" (#"prod" "A" (#"neg" "B"))) "e")))
                (#"hd" (#"neg" (#"prod" "A" (#"neg" "B")))))
            (#"val_subst"
                (#"id" (ext "H" (#"neg" "B")))
                (#"pair" "v" (#"hd" (#"neg" "B"))))))}})
