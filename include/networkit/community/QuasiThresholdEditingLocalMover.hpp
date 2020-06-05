#ifndef QUASITHRESHOLDEDITINGLOCALMOVER_H
#define QUASITHRESHOLDEDITINGLOCALMOVER_H

#include <networkit/graph/Graph.hpp>
#include <networkit/graph/DynamicForest.hpp>
#include <networkit/structures/Cover.hpp>
#include <networkit/auxiliary/SignalHandling.hpp>
#include <networkit/auxiliary/Log.hpp>

namespace NetworKit {
	
	


	class BucketQueue { 
		count nextNode;
		count currentBucket;
		std::vector<node> nodes;
		//points to first element in the bucket
		std::vector<count> border;
		
		public :
		BucketQueue(count n = 0) : nodes(n), border(n), nextNode(none), currentBucket(none){
		}
		
		
		void fill(const std::vector<node> &elements, const DynamicForest &dynamicForest){
			count maxDepth = 2 * elements.size();
			std::fill(border.begin(), border.begin() + std::min(maxDepth + 1, border.size()), 0);
			for (node u : elements) {
				if(dynamicForest.depth(u) > maxDepth) continue;
				border[dynamicForest.depth(u)] += 1;
			}
			for (int m = 1; m <= maxDepth; m++){
				border[m] += border[m-1];
			}
			currentBucket = maxDepth;
			nextNode = none;
			for(int j = elements.size() - 1; j >= 0; j--){
				node u = elements[j];
				if(dynamicForest.depth(u) > maxDepth){
					continue;
				}
				border[dynamicForest.depth(u)] -= 1;
				nodes[border[dynamicForest.depth(u)]] = u;
				nextNode += 1;
			}
		
			if(nextNode == none){
				return;
			} 

				
		}
		
		node next(){
			if(nextNode == none){
				return none;
			}
			node result = nodes[nextNode];
			while(nextNode < border[currentBucket]){
				currentBucket -= 1;
			}
			nextNode -= 1;
			return result;
		}
		
		void insertParent(node p){
			nextNode += 1;
			//first element of currentBucket
			count bucketBorder = border[currentBucket];
			node firstOfBucket = nodes[bucketBorder];
			nodes[nextNode] = firstOfBucket;
			nodes[bucketBorder] = p;
			border[currentBucket] += 1;
		}
		
		bool empty() {
			return nextNode == none;
		}
		
		std::string printQueue(){
			if(empty()){
				return "BucketQueue:";
			}
			std::stringstream ss;
			ss << "BucketQueue:";
			int j = 0;
			for (count i = 0; i <= nextNode; i++){
				while(border[j] == i){
					ss << "| ";
					j++;
				}
				ss << nodes[i] << " ";
			}
			return ss.str();
		}
		
		
	}; 



	class EditingRunner {
		public:
			/*~EditingRunner(){
			};*/
			EditingRunner(
				const Graph& G, 
				Graph forest, 
				count maxIterations,
				bool sortPaths,
				bool randomness,
				std::vector<NetworKit::node> order,
				count maxPlateauSize,
				bool insertRun) :
				G(G),
				forest(forest),
				maxIterations(maxIterations),
				usedIterations(0),
				sortPaths(sortPaths),
				randomness(randomness),
				order(order),
				maxPlateauSize(maxPlateauSize),
				insertRun(insertRun),
				handler(),
				dynamicForest(forest),
				hasMoved(1),		
				rootEqualBestParents(1),
				plateauSize(0),
				dist(){
				
				handler.assureRunning();
				bucketQueue = BucketQueue(G.upperNodeIdBound());
				
				numEdits = countNumberOfEdits();
				editsBefore = countNumberOfEdits();

				marker = std::vector<bool>(G.upperNodeIdBound(), false);
				bestParentBelow = std::vector<node>(G.upperNodeIdBound(), none);
				lastVisitedDFSNode = std::vector<node>(G.upperNodeIdBound(), none);
				G.parallelForNodes([&](node u) {
					lastVisitedDFSNode[u] = u;
				});
				scoreMax = std::vector<count> (G.upperNodeIdBound(), 0);
				childCloseness = std::vector<count> (G.upperNodeIdBound(), 0);
				nodeTouched  = std::vector<bool>(G.upperNodeIdBound(), false);
				equalBestParents = std::vector<count> (G.upperNodeIdBound(), 1);
				if(insertRun){
					existing = std::vector<bool>(G.upperNodeIdBound(), 0);
				} else {
					existing = std::vector<bool>(G.upperNodeIdBound(), 1);
				}
			};
			void runLocalMover(){
				handler.assureRunning();
				count i;
				if(insertRun){
					i = 0;
				} else {
					i = 1;
				}
				for (; hasMoved && i <= maxIterations; ++i) {
					if(!hasMoved || (randomness && plateauSize > maxPlateauSize)) break;
					handler.assureRunning();
					hasMoved = false;

					if(insertRun){
						for(index j = 0; j < G.upperNodeIdBound();j++){
							node nodeToMove = order[j];
							localMove(nodeToMove);
							existing[nodeToMove] = 1;
						}
						insertRun = 0;
					} else {
						G.forNodesInRandomOrder([&](node nodeToMove) {
							localMove(nodeToMove);
						});
					}
					usedIterations = i;

				if(countNumberOfEdits() == editsBefore){
					plateauSize++;
				}	else {
					plateauSize = 0;
				}
				editsBefore = countNumberOfEdits();
				}

				forest = dynamicForest.toGraph();

				assert(numEdits == countNumberOfEdits());
			};
			
			NetworKit::Cover getCover(index mergeDepth) const {
				Cover c(G.upperNodeIdBound());


				std::vector<count> depth(G.upperNodeIdBound());

				index curSubset = none;

				dynamicForest.dfsFrom(none, [&](node u) {
					if (u != none) {
						if (dynamicForest.parent(u) == none) {
							depth[u] = 0;
						} else {
							depth[u] = depth[dynamicForest.parent(u)] + 1;
						}

						if (depth[u] == mergeDepth || (depth[u] < mergeDepth && dynamicForest.nextDFSNodeOnEnter(u, u) == u)) {
							curSubset = c.toSingleton(u);

							node p = dynamicForest.parent(u);
							while (p != none) {
								c.addToSubset(curSubset, p);
								p = dynamicForest.parent(p);
							}
						} else if (depth[u] > mergeDepth) {
							c.addToSubset(curSubset, u);
						}
					}
				}, [&](node) {
				});

				return c;
			};
			
			count getNumberOfEdits() const {
				return numEdits;
			};
			
			count getUsedIterations() const {
				return usedIterations;
			};
			
			Graph getForest() const {
				return forest;
			};
			
			
			
			
		private:			
			const Graph& G;
			Graph forest;
			count maxIterations;
			count usedIterations;
			bool sortPaths;
			bool randomness;
			std::vector<NetworKit::node> order;
			count maxPlateauSize;
			
			bool insertRun;
			count numEdits;
			
			
			Aux::SignalHandler handler;
			DynamicForest dynamicForest;
			bool hasMoved;
			std::vector<bool> marker;

			NetworKit::BucketQueue bucketQueue;
			std::vector<node> neighbors;
			std::vector<node> touchedNodes;
			std::vector<node> lastVisitedDFSNode;
			std::vector<node> bestParentBelow;

			std::vector<count> scoreMax;
			std::vector<count> childCloseness;
			std::vector<bool> nodeTouched;
			
			count bestParent;
			count rootScoreMax;
			count rootChildCloseness;
			
			count bestEdits;
			count curEdits;
			node curParent;
			std::vector<node> curChildren;
			std::vector<node> bestChildren;
			
			std::vector<bool> existing;
			std::vector<count> equalBestParents;
			count rootEqualBestParents;
			
			count editsBefore;
			count plateauSize;
			
			count maxDepth;
			
			std::mt19937_64& gen = Aux::Random::getURNG();
			std::uniform_int_distribution<count> dist;
			
			void localMove(node nodeToMove){
				assert(numEdits == countNumberOfEdits());
				TRACE("Move node ", nodeToMove);
				handler.assureRunning();
				G.forEdgesOf(nodeToMove, [&](node v) {
					if(existing[v]){
						marker[v] = true;
						neighbors.push_back(v);
						if(sortPaths) {
							dynamicForest.moveUpNeighbor(v, nodeToMove);
						}
					}
				});
				if(sortPaths) {
					dynamicForest.moveUpNeighbor(nodeToMove, nodeToMove);
				}
				curChildren = dynamicForest.children(nodeToMove);
				curParent = dynamicForest.parent(nodeToMove);
				if(insertRun){
					maxDepth = 2 * neighbors.size();
					curEdits = neighbors.size();
				} else {
					maxDepth = 2 * neighbors.size();
					curEdits = G.degree(nodeToMove);
					dynamicForest.dfsFrom(nodeToMove, [&](node c) {
						if (c != nodeToMove) {
							curEdits += 1 - 2 * marker[c];
						}
					}, [](node){});
					for (node p = dynamicForest.parent(nodeToMove); p != none; p = dynamicForest.parent(p)) {
						curEdits += 1 - 2 * marker[p];
					}
				}
				dynamicForest.isolate(nodeToMove);
				bucketQueue.fill(neighbors, dynamicForest);
				bestChildren.clear();
				bestParent = none;
				rootScoreMax = 0;
				rootChildCloseness = 0;
				//all neighbors to deep
				if(bucketQueue.empty()) {
					bestParent = none;
					bestEdits = neighbors.size();
					TRACE("Isolate");
				} else {
					while(!bucketQueue.empty()){
						node u = bucketQueue.next();
						processNode(u, nodeToMove);
					}
					bestEdits = neighbors.size() - rootScoreMax;
					if (rootChildCloseness > rootScoreMax) {
						bestParent = none;
						bestEdits = neighbors.size() - rootChildCloseness;
					} 
					
					
					for (node u : touchedNodes) {
						if (u != nodeToMove && dynamicForest.parent(u) == bestParent && childCloseness[u] != none) {
							if(childCloseness[u] > 0 || (randomness &&  randomBool(2))){
								bestChildren.push_back(u);
							}
						}
					}
				}
				


			#ifndef NDEBUG
				compareWithQuadratic(nodeToMove);
			#endif

				// calculate the number of saved edits as comparing the absolute number of edits doesn't make sense
				count savedEdits = curEdits - bestEdits;

				// cleanup for linear move
				for (node u : touchedNodes) {
					equalBestParents[u] = 1;
					lastVisitedDFSNode[u] = u;
					scoreMax[u] = 0;
					childCloseness[u] = 0;
					nodeTouched[u] = false;
					bestParentBelow[u] = none;
				}

				neighbors.clear();
				touchedNodes.clear();
				rootEqualBestParents = 0;

				G.forEdgesOf(nodeToMove, [&](node v) {
					marker[v] = false;
				});
				
				
				

				if (savedEdits > 0 || (savedEdits == 0 && randomness)) {
					dynamicForest.moveToPosition(nodeToMove, bestParent, bestChildren);

					hasMoved = true;
					numEdits -= savedEdits;

			#ifndef NDEBUG
					forest = dynamicForest.toGraph();
					assert(numEdits == countNumberOfEdits());
			#endif
				} else  {
					dynamicForest.moveToPosition(nodeToMove, curParent, curChildren);
					#ifndef NDEBUG
							forest = dynamicForest.toGraph();
							assert(numEdits == countNumberOfEdits());
					#endif
				}
			};
			
			void processNode(node u, node nodeToMove){
					TRACE("Processing node ", u, " of depth ", dynamicForest.depth(u), " (node to move: ", nodeToMove, ")");
					TRACE("Parent: ", dynamicForest.parent(u), ", children: ", dynamicForest.children(u));
					assert(u != nodeToMove);
					assert(dynamicForest.depth(u) <= maxDepth);
					if (!nodeTouched[u]) {
						nodeTouched[u] = true;
						touchedNodes.emplace_back(u);
						assert(marker[u]); // only marked neighbors may be processed without having been touched before
					}

					count sumPositiveEdits = childCloseness[u];
					assert(childCloseness[u] != none);

					childCloseness[u] += marker[u];
					childCloseness[u] -= 1 - marker[u]; // if (marker[u]) { ++childCloseness[u]; } else { --childCloseness[u]; }

					TRACE("Edit difference before descending: ", childCloseness[u]);

					assert(!marker[u] || childCloseness[u] > 0);

					if (childCloseness[u] != none) {
						assert(lastVisitedDFSNode[u] == u);

						node c = dynamicForest.nextDFSNodeOnEnter(u, u);

						while (c != u) {

							if (!nodeTouched[c] || childCloseness[c] == none) {
								
								if(dynamicForest.depth(c) > maxDepth){
									childCloseness[u] = none;
								} else {
									--childCloseness[u];
								}
								
								// advance to the next starting point for the DFS search.
								c = lastVisitedDFSNode[c];

								if (childCloseness[u] == none) {
									lastVisitedDFSNode[u] = c;
									break;
								}

								c = dynamicForest.nextDFSNodeOnEnter(c, u);
							} else {
								node p = dynamicForest.parent(c);
								c = dynamicForest.nextChild(c, p);

								while (c == p && c != u) {
									p = dynamicForest.parent(p);
									c = dynamicForest.nextChild(c, p);
								}
							}
						}
					}

					TRACE("Edit difference after descending: ", childCloseness[u]);

					if (sumPositiveEdits > scoreMax[u] || scoreMax[u] == 0) {
						scoreMax[u] = sumPositiveEdits;
						bestParentBelow[u] = u;
					}

					assert(scoreMax[u] != none);

					scoreMax[u] += marker[u];

					if (scoreMax[u] > 0) {
						scoreMax[u] -= 1 - marker[u];
					}

					TRACE("Maximum gain at ", u, ": ", scoreMax[u]);
					if (scoreMax[u] > 0 || (childCloseness[u] != none && childCloseness[u] != 0)) {
						node p = dynamicForest.parent(u);
						if (p != none) {
							assert(dynamicForest.depth(p) <= maxDepth);
							if (!nodeTouched[p]) {
								nodeTouched[p] = true;
								touchedNodes.push_back(p);
								if(!marker[p]){ //neighbors already in queue
									bucketQueue.insertParent(p);
								} 
							}

							if (childCloseness[u] != none) {
								assert(childCloseness[u] <= scoreMax[u]);
								childCloseness[p] += childCloseness[u];
							}
							bool coin = 0;
							if(randomness && (scoreMax[u] == scoreMax[p])){
								equalBestParents[p]+=equalBestParents[u];
								coin = randomBool(equalBestParents[p]);
							}
							if (scoreMax[u] > scoreMax[p] || coin) {
								scoreMax[p] = scoreMax[u];
								bestParentBelow[p] = bestParentBelow[u];
							}
							if (scoreMax[u] > scoreMax[p]){
								equalBestParents[p] = equalBestParents[u];
							}
						} else {
							bool coin = 0;
							if(randomness && (scoreMax[u] == rootScoreMax)){
								rootEqualBestParents+=equalBestParents[u];
								coin = randomBool(rootEqualBestParents);
							}
							if (scoreMax[u] > rootScoreMax || coin) {
								rootScoreMax = scoreMax[u];
								bestParent = bestParentBelow[u];
							}
							if (scoreMax[u] > rootScoreMax){
								rootEqualBestParents = equalBestParents[u];					
							}
							if (childCloseness[u] != none) {
								rootChildCloseness += childCloseness[u];
							}
						}
					}

					if (dynamicForest.children(u).empty()) { assert(childCloseness[u] == 1); }
			};
			
			void compareWithQuadratic(node nodeToMove) const {
				std::vector<count> missingBelow, missingAbove, existingBelow, existingAbove;
							missingBelow.resize(G.upperNodeIdBound(), 0);
							missingAbove.resize(G.upperNodeIdBound(), 0);
							existingBelow.resize(G.upperNodeIdBound(), 0);
							existingAbove.resize(G.upperNodeIdBound(), 0);
							std::vector<bool> usingDeepNeighbors(G.upperNodeIdBound(), false);

							dynamicForest.forChildrenOf(none, [&](node r) {
								if(existing[r]){
									dynamicForest.dfsFrom(r,
										[&](node u) {
											if(dynamicForest.depth(u) > maxDepth) usingDeepNeighbors[u] = true;
											if (u != nodeToMove) {
												missingBelow[u] = missingAbove[u] = 1 - marker[u];
												existingBelow[u] = existingAbove[u] = marker[u];
											}
											node p = dynamicForest.parent(u);
											if (p != none) {
												missingAbove[u] += missingAbove[p];
												existingAbove[u] += existingAbove[p];
											}
										},
										[&](node u) {
											node p = dynamicForest.parent(u);
											if (p != none) {
												missingBelow[p] += missingBelow[u];
												existingBelow[p] += existingBelow[u];
												if(usingDeepNeighbors[u]) usingDeepNeighbors[p] = true;
											}
										});
								}
							});

							assert(missingBelow[nodeToMove] == 0);
							assert(existingBelow[nodeToMove] == 0);

							bool exactValue = true;
							for (node c : curChildren) {
								missingBelow[nodeToMove] += missingBelow[c];
								existingBelow[nodeToMove] += existingBelow[c];
								if(usingDeepNeighbors[c]) exactValue = false;
							}

							if (curParent != none) {
								missingAbove[nodeToMove] = missingAbove[curParent];
								existingAbove[nodeToMove] = existingAbove[curParent];
								if(usingDeepNeighbors[curParent]) exactValue = false;
							}
						if(exactValue){
							assert(curEdits == neighbors.size() - existingAbove[nodeToMove] - existingBelow[nodeToMove] + missingAbove[nodeToMove] + missingBelow[nodeToMove]);
						}

						count minEdits = curEdits;
						std::vector<node> minChildren;
						node minParent = curParent;
						G.forNodes([&](node u) {
							if (u == nodeToMove || usingDeepNeighbors[u] || !existing[u]) return;
							if (existingBelow[u] >= missingBelow[u] || (childCloseness[u] > 0 && childCloseness[u] != none)) {
								assert(childCloseness[u] == existingBelow[u] - missingBelow[u]);
							} else if (nodeTouched[u]) {
								assert(childCloseness[u] == none);
							}
						});

						G.forNodes([&](node u) {
							if (dynamicForest.children(u).empty() && marker[u] && !usingDeepNeighbors[u] &&  existing[u]) {
								assert(childCloseness[u] == 1);
							}
						});

						auto tryEditBelow = [&](node p) {
							if (p == nodeToMove) return;

							count edits = neighbors.size();
							if (p != none) {
								edits += missingAbove[p];
								edits -= existingAbove[p];
							}

							std::vector<node> children;
							dynamicForest.forChildrenOf(p, [&](node c) {
								if (c == nodeToMove || usingDeepNeighbors[c] || !existing[c]) return;
								if (existingBelow[c] > missingBelow[c]) { // TODO try >= (more children...)
									if (dynamicForest.children(c).empty() && marker[c]) {
										assert(childCloseness[c] == 1);
									}
									assert(childCloseness[c] == existingBelow[c] - missingBelow[c]);

									children.emplace_back(c);
									edits -= existingBelow[c] - missingBelow[c];
								}
							});

							if (edits < minEdits) {
								minEdits = edits;
								minChildren = std::move(children);
								minParent = p;
							}
						};

						dynamicForest.dfsFrom(none, [](node){}, tryEditBelow);
						tryEditBelow(none);

						assert(minEdits >= bestEdits);

						count childClosenessControl = neighbors.size();
						if (bestParent != none) {
							childClosenessControl -= (existingAbove[bestParent] - missingAbove[bestParent]);
						}
						for (node u : bestChildren) {
							childClosenessControl -= (existingBelow[u] - missingBelow[u]);
						}
						TRACE("Current edits: ", curEdits, " (with parent ", curParent, " and current children ", curChildren, "), minimum edits: ", minEdits);
						TRACE("Quadratic algorithm wants to have new parent ", minParent, " and new children ", minChildren);
						TRACE("Linear algorithm wants to have new parent ", bestParent, " and new children ", bestChildren, " edits: ", childClosenessControl);
						assert(minEdits >= childClosenessControl);
			};
			
			NetworKit::count countNumberOfEdits() const {
				// count number of edits that are needed with the initial given forest
				count numExistingEdges = 0;
				count numMissingEdges = 0;
				std::vector<bool> marker(G.upperNodeIdBound());

				dynamicForest.forChildrenOf(none, [&](node r) {
					count depth = 0;
					dynamicForest.dfsFrom(r,
					[&](node u) { // on enter
						count upperNeighbors = 0;

						G.forNeighborsOf(u, [&](node v) {
							if (marker[v]) {
								++upperNeighbors;
							}
						});

						numExistingEdges += upperNeighbors;
						numMissingEdges += depth - upperNeighbors;

						marker[u] = true;
						depth += 1;
					},
					[&](node u) { // on exit
						marker[u] = false;
						depth -= 1;
					});
				});

				return numMissingEdges + (G.numberOfEdges() - numExistingEdges);
			};
			
			
			NetworKit::count editsIncidentTo(node u) const {
				std::vector<bool> visited(G.upperNodeIdBound());
				count edits = 0;
				node parent = dynamicForest.parent(u);
				while(parent != none){
					visited[parent] = 1;
					if(!G.hasEdge(parent, u)){
						edits++;
					}
					parent = dynamicForest.parent(parent);
				}
				dynamicForest.forChildrenOf(u, [&](node c) {
					dynamicForest.dfsFrom(c,
					[&](node w) {
						visited[w] = 1; 
						if(!G.hasEdge(w, u)){
							edits++;
						}
					},
					[&](node w) {});
				});
				
				G.forNeighborsOf(u, [&](node w) {
					if (!visited[w]) {
						edits++;
					}
				});

				return edits;
			};
			
			bool randomBool(count options) {
				//count x = dist(gen);
				count x = dist(gen, std::uniform_int_distribution<count>::param_type(0, options-1));
				return options == 0 ? 0 : rand() % options == 0;
			};
			
			
			

			
		
	};
	

class QuasiThresholdEditingLocalMover {
public:
	QuasiThresholdEditingLocalMover(const NetworKit::Graph &G, 
		const std::vector< NetworKit::node > &parent = std::vector<NetworKit::node>(), 
		NetworKit::count maxIterations = 2,  
		bool sortPaths = true,
		bool randomness = false,
		const std::vector< NetworKit::node > &order = std::vector<NetworKit::node>(),
		count maxPlateauSize = 4);

	void run();

	Graph getQuasiThresholdGraph() const;
	count getNumberOfEdits() const;
	count getUsedIterations() const;
	count getPlateauSize() const;
	std::vector<node> getParents() const;
	Cover getCover(NetworKit::index mergeDepth) const;
private:

	const Graph& G;
	Graph forest;
	count maxIterations;
	bool sortPaths;
	bool randomness;
	std::vector<NetworKit::node> order;
	count maxPlateauSize;
	bool insertRun;
	
	count usedIterations;
	count numEdits;
	
	EditingRunner* runner;

	
};


} // namespace NetworKit

#endif // QUASITHRESHOLDEDITINGLOCALMOVER_H