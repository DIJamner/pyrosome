#todo: clean if makefile exists
coq_makefile -f _CoqProject -o Makefile
cd ./coqutil
make -j$1
cd ..
cd ./canonical-binary-tries
make -j$1
cd ..
make -j$1
