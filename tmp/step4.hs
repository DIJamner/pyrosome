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
            (#"exch" "H" (ext (#"only" (#"neg" "B")) (#"neg" (#"prod" "A" (#"neg" "B")))))
            (#"jmp"
                (#"val_subst"
                    (#"vsub"
                        (#"cont"
                            "A"
                            (#"blk_subst"
                                (#"csub"
                                    (#"exch" (#"only" (#"neg" "B")) (#"only" (#"neg" (#"prod" "A" (#"neg" "B")))))
                                    (#"id" (#"only" "A")))
                                (#"jmp"
                                    (#"hd" (#"neg" (#"prod" "A" (#"neg" "B"))))
                                    (#"val_subst"
                                        (#"exch" (#"only" (#"neg" "B")) (#"only" "A"))
                                        (#"pair" (#"hd" "A") (#"hd" (#"neg" "B"))))))))
                    (#"hd" (#"neg" "A")))
                (#"val_subst"
                    (#"id" "H")
                    "v"))))}})