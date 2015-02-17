all: predict

predict: main.cpp predictor.cpp format.cpp knn.cpp nbayes.cpp rforest.cpp tfidf.cpp dtree.cpp
	g++ -std=c++11 -g -Wall $< -o $@

clean:
	rm predict
