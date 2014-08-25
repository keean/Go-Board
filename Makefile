all : go

go : go.cpp
	rm -f *.gcda
	touch go.cpp
	g++ -o go -std=gnu++11 -march=native -O3 -fprofile-generate -fwhole-program go.cpp -Wa,-q
	./go
	touch go.cpp
	g++ -o go -std=gnu++11 -march=native -O3 -fprofile-use -fwhole-program go.cpp -Wa,-q

clean:
	rm -f go *.o *.gcda
