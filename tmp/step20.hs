(!! {{e #"blk_subst"
    (#"exch" "G" (ext "H" (#"neg" "B")))
    (#"blk_subst"
        (#"csub"
            (#"id" (ext "H" (#"neg" "B")))
            (#"vsub"
                (#"cont"
                    (#"prod" "A" (#"neg" "B"))
                    (#"pm_pair" (#"hd" (#"prod" "A" (#"neg" "B"))) "e"))))
        (#"blk_subst"
            (#"exch" (ext "H" (#"neg" "B")) (#"only" (#"neg" (#"prod" "A" (#"neg" "B")))))
                (#"jmp"
                    (#"hd" (#"neg" (#"prod" "A" (#"neg" "B"))))
                    (#"pair" "v" (#"hd" (#"neg" "B"))))))}})
