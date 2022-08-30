#todo: clean if makefile exists
coq_makefile -f _CoqProject -o Makefile
cd ./canonical-binary-tries
make -j$1
cd ..
cd ./bedrock2
git submodule update --init
make bedrock2_noex -j$1
cd ..
make -j$1
