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
            (#"cmp"
                (#"csub" (#"vsub" "v") (#"id" (ext (#"neg" "B") (#"neg" (#"prod" "A" (#"neg" "B"))))))
                (#"cmp"
                    (#"csub"
                        (#"id" "A")
                        (#"exch" (#"only" (#"neg" "B")) (#"only" (#"neg" (#"prod" "A" (#"neg" "B"))))))
                    (#"csub"
                        (#"exch" (#"only" "A") (#"only" (#"neg" (#"prod" "A" (#"neg" "B")))))
                        (#"id" (#"only" (#"neg" "B"))))))
            (#"jmp"
                (#"hd" (#"neg" (#"prod" "A" (#"neg" "B"))))
                (#"pair" (#"hd" "A") (#"hd" (#"neg" "B"))))))}})
