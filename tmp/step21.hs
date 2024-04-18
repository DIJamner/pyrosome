(!! {{e #"blk_subst"
    (#"exch" "G" (ext "H" (#"neg" "B")))
    (#"blk_subst"
        (#"exch" (ext "H" (#"neg" "B")) "G")
        (#"blk_subst"
            (#"csub"
                (#"vsub"
                    (#"cont"
                        (#"prod" "A" (#"neg" "B"))
                        (#"pm_pair" (#"hd" (#"prod" "A" (#"neg" "B"))) "e")))
                (#"id" (ext "H" (#"neg" "B"))))
            (#"jmp"
                (#"hd" (#"neg" (#"prod" "A" (#"neg" "B"))))
                (#"pair" "v" (#"hd" (#"neg" "B"))))))}})