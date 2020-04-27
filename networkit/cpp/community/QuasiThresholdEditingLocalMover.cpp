/*
 *
 */

#include <unordered_set>

#include <networkit/community/QuasiThresholdEditingLocalMover.hpp>
#include <networkit/generators/TreeReachabilityGraphGenerator.hpp>
#include <networkit/graph/DynamicForest.hpp>
#include <networkit/graph/GraphTools.hpp>
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
	BucketQueue(count n){
		nodes = std::vector<node>(n);
		border = std::vector<count>(n);
		nextNode = none;
		currentBucket = none;
	}
	
	
	void fill(std::vector<node> elements, std::vector<count> depth){
		std::fill(border.begin(), border.end(), 0);
		count max_depth = 0;
		for (node u : elements) {
			border[depth[u]] += 1;
			max_depth = std::max(max_depth, depth[u]);
		}
		for (int m = 1; m <= max_depth; m++){
			border[m] += border[m-1];
		}
    nextNode = none;
		currentBucket = none;
		TRACE("Border Array ", border);
		for(int j = elements.size() - 1; j >= 0; j--){
			node u = elements[j];
			border[depth[u]] -= 1;
    	nodes[border[depth[u]]] = u;
			nextNode += 1;
  	}
		if(nextNode == none){
			TRACE("Bucket queue initially empty");
			return;
		} 
		currentBucket = max_depth;
		/*if(currentBucket > 2 * elements.size()){
			nextNode = border[(2 * elements.size()) + 1];
			if(nextNode == 0) {
				nextNode = none;
				TRACE("Bucket queue initially empty");
				return;
			} else {
				nextNode -= 1;
			}
			currentBucket = depth[nextNode];
		}*/
		TRACE("Constructed bucket queue", nodes, " from elements ", elements);
		TRACE("Borders: ", border);
		TRACE("Starting with: ", nodes[nextNode], " in bucket ", currentBucket);
		//assert(currentBucket <= 2 * elements.size());
		/*if(nextNode != 0){
			for (int i = 1; i<= nextNode; i++){
				assert(depth[nodes[i-1]] <= depth[nodes[i]]);
			}
		}*/
			
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
		TRACE("Move ", firstOfBucket, " to ", nextNode);
		TRACE("Insert ", p, " to Bucket queue at pos ", bucketBorder);
	}
	
	bool empty() {
		return nextNode == none;
	}
	
	
};

class NaiveUnionFind {
	std::vector<node> representative;
	
public:
	NaiveUnionFind (count n){
		representative =  std::vector<node>(n, none);
	}
	
	node find (node x) {
		if(representative[x] == none){
			return x;
		} else {
			return find(representative[x]);
		}
	}
	
	void unionNaive(node u, node v){
		representative[find(u)] = find(v);
	}

	
};
class SimplePathState {
	std::vector<count> path_membership;
	std::vector<count> pos;
	std::vector<std::vector<node>> paths;
	std::vector<count> neighborCount;
	std::vector<count> pathLength;
	std::stack<count> freeList;
	bool isSorted;
	
	
	
	//does not maintain sorting
	void moveToPath(node u, count newPathId){
		count oldPathId = path_membership[u];
		assert(oldPathId != newPathId);
		count oldPos = pos[u];
		assert(pathLength[oldPathId] > oldPos);
		pathLength[oldPathId] -= 1;
		bool isNeighbor = oldPos < neighborCount[oldPathId];
		if(isNeighbor){
			neighborCount[oldPathId] -=1;
			node lastNeighbor = paths[oldPathId][neighborCount[oldPathId]];
			if(lastNeighbor != u){
				pos[u] = pos[lastNeighbor];
				paths[oldPathId][pos[lastNeighbor]] = u;
				pos[lastNeighbor] = oldPos;
				paths[oldPathId][oldPos] = lastNeighbor;	
				oldPos = pos[u];
			}
		}
		node lastNode = paths[oldPathId][pathLength[oldPathId]];
		if(lastNode != u){
			assert(pathLength[oldPathId] > 0);
			pos[lastNode] = pos[u];
			paths[oldPathId][pos[u]] = lastNode;	
		} else if(pathLength[oldPathId] == 0){
			freeList.push(oldPathId);	
		}
		count newPos = pathLength[newPathId];
		if(isNeighbor){
			if(neighborCount[newPathId] != pathLength[newPathId]){
				newPos = neighborCount[newPathId];
				node firstNonNeighbor = paths[newPathId][newPos];
				pos[firstNonNeighbor] = pathLength[newPathId];
				paths[newPathId][pathLength[newPathId]] = firstNonNeighbor;
			}
			neighborCount[newPathId] += 1;
		}
		paths[newPathId][newPos] = u;
		pathLength[newPathId] += 1;	
		pos[u] = newPos;
		path_membership[u] = newPathId;

	}
	
	void findSimplePathsBelow(node u, DynamicForest dynamicForest, NaiveUnionFind* uf){
		std::vector<node> children = dynamicForest.children(u);
		if(children.size() == 1 && u != none){
			uf->unionNaive(children[0], u);
		}
		for(node child : children){
			findSimplePathsBelow(child, dynamicForest, uf);
		}
	}
	
	std::string printPath(count pathId){
		std::stringstream ss;
		if(pathLength[pathId] > 0){
			std::vector<node> path = paths[pathId];
			if(neighborCount[pathId] == 0){
				ss << " [|" << path[0];
			} else {
				ss << " [" << path[0];
			}
			for (count j = 1; j < pathLength[pathId]; j++){
				if(neighborCount[pathId] == j){
					ss << ",| " << path[j];
				} else {
					ss << ", " << path[j];
				}
			}
			if(pathLength[pathId] == 1 && neighborCount[pathId] == 1){
				ss << "|]";
			} else {
				ss << "]";
			}
		}
		return ss.str();
	}
	
	bool isProper(){
		for(count p = 0; p < paths.size(); p++){
			assert(neighborCount[p] <= pathLength[p]);
			std::vector<node> path =  paths[p];
			for(int i = 0; i < pathLength[p]; i++){
				node u = path[i];
				if(u == none){
					return false;
				}
				if(path_membership[u] != p){
					return false;
				}
				if(pos[u] != i){
					return false;
				}
			}
		}
		return true;
	}
	
	
public:
	
	SimplePathState(count n) {
		path_membership = std::vector<count>(n);
		pos = std::vector<count>(n);
		paths = std::vector<std::vector<node>>(n, std::vector<node>(n, none));
		neighborCount = std::vector<count>(n, 0);
		pathLength = std::vector<count>(n, 1);
		freeList = std::stack<count>();
		for (node i = 0; i < n; i++){
			path_membership[i] = i;
			pos[i] = 0;
			paths[i][0] = i;
		}
		assert(isProper());

	}
	
	SimplePathState(DynamicForest dynamicForest, count n){
		NaiveUnionFind uf(n);
		std::vector<node> roots;
		
		for(node i = 0; i < n; i++){
			if(dynamicForest.parent(i) == none){
				roots.push_back(i);
			}
		}
		
		for(node root : roots) {
			findSimplePathsBelow(root, dynamicForest, &uf);
		}
		
		
		
		path_membership = std::vector<count>(n);
		pos = std::vector<count>(n);
		paths = std::vector<std::vector<node>>(n, std::vector<node>(n, none));
		neighborCount = std::vector<count>(n, 0);
		pathLength = std::vector<count>(n, 0);
		freeList = std::stack<count>();
		for (node u = 0; u < n; u++){
			count currentPathId = (count) uf.find(u);
			count currentPos = pathLength[currentPathId];
			path_membership[u] = currentPathId;
			pos[u] = currentPos;
			paths[currentPathId][currentPos] = u;
			pathLength[currentPathId] += 1;
		}
		
		
		for (count i = 0; i < n; i++){
			if (pathLength[i] == 0){
				freeList.push(i);
			}
		}
		
		for (node u = 0; u < n; u++){
			node parent = dynamicForest.parent(u);
			if(parent != none && dynamicForest.children(parent).size() == 1){
				assert(simplePath(u) ==  simplePath(parent));
			}
		}
		
		for(count p = 0; p < n; p++){
			if(pathLength[p] > 0){
				bool lastNode = 0;
				for(count i = 0; i < pathLength[p] - 1; i++){
					if(!lastNode && dynamicForest.children(paths[p][i]).size() != 1){
						lastNode = 1;
					} else {
						assert(dynamicForest.children(paths[p][i]).size() == 1);
					}				
				}
				}
			}
		assert(isProper());
		
	}
	
	std::string printPaths(){
		std::stringstream ss;
		ss << "Simple Paths:";
		for (count i = 0; i < paths.size(); i++){
			ss << printPath(i);
		}
		return ss.str();
	}
	
	
	
	void resetSorting() {
		std::fill(neighborCount.begin(), neighborCount.end(), 0);
	}
	
	void moveUp (node u) {
		count currentPathId = path_membership[u];
		count currentPos = pos[u];
		count nextPos = neighborCount[currentPathId];
		assert(nextPos < pathLength[currentPathId]);
		if(currentPos < nextPos) {
			//neighbor already counted and moved
			return;
		} else if (currentPos > nextPos) {
			node temp = paths[currentPathId][nextPos];
			assert(path_membership[temp] == path_membership[u]);
			pos[temp] = currentPos;
			pos[u] = nextPos;
			paths[currentPathId][currentPos] = temp;
			paths[currentPathId][nextPos] = u;
		}
		//in case of equality, only counter needs to be updated
		neighborCount[currentPathId]+=1;
		assert(isProper());
		
	}
	
	void splitPathOf(node u) {
		count pathId = path_membership[u];
		count neighbors = neighborCount[pathId];
		count nonNeighbors = pathLength[pathId] - neighborCount[pathId];
		//nothing to split
		if(neighbors == 0 || nonNeighbors == 0 || pathLength[pathId] < 2){
			return;
		}
		INFO("Split path of ", u);
		count newPathId = freeList.top();
		assert(pathLength[newPathId] == 0);
		freeList.pop();
		for(int i = 0; i < neighbors; i++){
			node u = paths[pathId][0];
			assert(path_membership[u] == pathId);
			moveToPath(u, newPathId);
			assert(path_membership[u] == newPathId);
		}
		assert(pathLength[newPathId] ==  neighbors);
		assert(pathLength[pathId] == nonNeighbors);
		assert(isProper());
	}
	
	void splitPathAfter(node u) {
		count pathId = path_membership[u];
		count splitPos = pos[u] + 1;
		count nonNeighbors = pathLength[pathId] - neighborCount[pathId];
		count l = pathLength[pathId];
		//nothing to split
		if(splitPos == l || l < 2){
			return;
		}
		INFO("Split path after ", u);
		count newPathId = freeList.top();
		assert(pathLength[newPathId] == 0);
		freeList.pop();
		for(int i = splitPos; i < l; i++){
			node u = paths[pathId][splitPos];
			assert(path_membership[u] == pathId);
			moveToPath(u, newPathId);
			assert(path_membership[u] == newPathId);
		}
		assert(isProper());
	}
	
	void unionPathsOf(node u, node v) {
		isSorted = 0;
		count secondPathId = path_membership[v];
		count firstPathId = path_membership[u];
		assert(pathLength[firstPathId] > 0);
		assert(pathLength[secondPathId] > 0);
		count sum = pathLength[firstPathId] + pathLength[secondPathId];
		if(firstPathId == secondPathId){
			return;
		}
		INFO("Union paths of ", u, " and ", v);
		count elementsToMove = pathLength[firstPathId];
		
		for (count i = 0; i < elementsToMove; i++) {
			node w = paths[firstPathId][0];
			assert(firstPathId == path_membership[w]);
			assert(pathLength[firstPathId] > 0 && pathLength[secondPathId] > 0);
			moveToPath(w, secondPathId);
			assert(path_membership[w] == secondPathId);
		}
		assert(pathLength[firstPathId] == 0);
		assert(pathLength[secondPathId] == sum);
		assert(isProper());
		
	}
	
	void isolate(node u) {
		count oldPathId = path_membership[u];
		count length = pathLength[oldPathId];
		if(length > 1){
			INFO("Isolate ", u);
			count newPathId = freeList.top();
			assert(pathLength[newPathId] == 0);
			freeList.pop();
			moveToPath(u, newPathId);
			assert(pathLength[newPathId] == 1);
			assert(pathLength[oldPathId] == (length - 1));
		}
		assert(isProper());
		
		
	}
	
	bool equals (SimplePathState other){
		assert(isProper());
		assert(other.isProper());
		if(other.upperNodeIdBound() != paths.size()){
			return 0;
		}
		for(count p = 0; p < paths.size(); p++){
			if(pathLength[p] > 0){
				std::vector<node> thisPath(&paths[p][0],&paths[p][pathLength[p]]);
				std::vector<node> otherPath = other.simplePath(thisPath[0]);
				std::sort(thisPath.begin(), thisPath.end(), [](const node & a, const node & b) -> bool
				{ return (long) a < (long) b; });
				std::sort(otherPath.begin(), otherPath.end(), [](const node & a, const node & b) -> bool
				{ return (long) a < (long) b; });
				if(thisPath != otherPath){
					INFO("Unequal paths ", thisPath, " and ", otherPath);
					return 0;
				}
			}
		}
		return 1;
	}
	
	
	std::vector<node> simplePath(node u){
		count pathId = path_membership[u];
		std::vector<node> result(&paths[pathId][0],&paths[pathId][pathLength[pathId]]);
		return result;
	}
	
	count upperNodeIdBound(){
		return paths.size();
	}
	
	DynamicForest reorderForest(DynamicForest dynamicForest){
		DynamicForest updatedForest = dynamicForest;
		assert(equals(SimplePathState(dynamicForest, paths.size())));
		for(count p = 0; p < paths.size(); p++){
			count l = pathLength[p];
			if(l > 1){
				for(count i = 0; i < l; i++){
					node u = paths[p][i];
					//u was first vertex in old ordering
					if(dynamicForest.parent(u) == none || dynamicForest.children(dynamicForest.parent(u)).size() != 1){
						updatedForest.setParent(paths[p][0], dynamicForest.parent(u));
					}
					//u was last vertex in old ordering
					if(dynamicForest.children(u).size() != 1){
						for(node child : dynamicForest.children(u)){
							updatedForest.setParent(child, paths[p][l - 1]);
						}
					}
					if(i > 0){
						updatedForest.setParent(u, paths[p][i-1]);
					}
				}
			}
		}
		

		/*INFO(printPaths());
		SimplePathState simplePathResults(updatedForest, paths.size());
		INFO(simplePathResults.printPaths());
		assert(equals(simplePathResults));*/
		return updatedForest;
	}
	
};  
}



NetworKit::QuasiThresholdEditingLocalMover::QuasiThresholdEditingLocalMover(const NetworKit::Graph &G, const std::vector< NetworKit::node > &parent, NetworKit::count maxIterations, bool moveSubtrees)
: G(G), maxIterations(maxIterations), moveSubtrees(moveSubtrees), numEdits(none) {
	forest = Graph(GraphTools::copyNodes(G), false, true);
	G.forNodes([&](node u) {
		if (parent[u] != none) {
			forest.addEdge(u, parent[u]);
		}
	});
}

void NetworKit::QuasiThresholdEditingLocalMover::run() {
	/*
	Idea: for each node check if it can be inserted below any other node such that the number of edits is reduced.
	Additionally check if the node should become a root node and add any number of previous roots as children.
	For each child of the new parent check if it can be inserted below the moved node. Question: is this possible such that the total time for the move is linear?

	For a node that shall be moved, mark all neighbors in the original graph.
	For just checking if a node can be inserted as leaf under an anchor node or as parent of an anchor node only the neighbors of that anchor node need to be iterated
	and checked for the mark, then the number of necessary edits can be determined.

	Problem: In order to keep these checks easy we should remove the node from the graph. Therefore insertion in the previous position must remain possible. This means that
	we need to be able to add arbitrary children the node previously had. We find them when iterating over the neighbors of the parent.
	But can we determine which of them should be added?

	Another idea: Keep an efficient forest data structure (or simply rooted trees in a graph + a list of roots?) that allows walking up and down in the tree.
	Then do DFS in order to discover possible inserts/deletes.
	This should actually allow to determine which children to take. Furthermore then probably we don't need to store the inserted edges explicitly but we can determine
	them again whenever we delete a node as we iterate over its neighbors anyway and we can in the same turn also iterate over the tree and determine which neighbors were there
	and which were not by checking for marked nodes.
	*/

	Aux::SignalHandler handler;

	DynamicForest dynamicForest(forest);

	numEdits = countNumberOfEdits();
	usedIterations = 0;

	bool hasMoved = true;
	std::vector<bool> marker(G.upperNodeIdBound());

	std::vector<count> numNeighbors;

	if (moveSubtrees) {
		numNeighbors.resize(G.upperNodeIdBound(), 0);
	}

	std::vector<count> depth(G.upperNodeIdBound(), 0);
	dynamicForest.dfsFrom(none, [&](node c) {
		if (c != none && dynamicForest.parent(c) != none) {
			depth[c] = depth[dynamicForest.parent(c)] + 1;
		}
	}, [](node){});

	handler.assureRunning();

	NetworKit::BucketQueue bucketQueue(G.upperNodeIdBound());
	NetworKit::SimplePathState simplePaths(dynamicForest, G.upperNodeIdBound());
	std::vector<node> neighbors, currentLevel, touchedNodes, lastVisitedDFSNode(G.upperNodeIdBound(), none), bestParentBelow(G.upperNodeIdBound(), none);
	G.parallelForNodes([&](node u) {
		lastVisitedDFSNode[u] = u;
	});
	std::vector<count> maxGain(G.upperNodeIdBound(), 0), editDifference(G.upperNodeIdBound(), 0);
	std::vector<bool> nodeTouched(G.upperNodeIdBound(), false);

	for (count i = 0; hasMoved && i < maxIterations; ++i) {
		handler.assureRunning();
		hasMoved = false;

		G.forNodesInRandomOrder([&](node nodeToMove) {
			handler.assureRunning();
			simplePaths.resetSorting();
			G.forEdgesOf(nodeToMove, [&](node v) {
				marker[v] = true;
				simplePaths.moveUp(v);
			});
			simplePaths.moveUp(nodeToMove);
			dynamicForest = simplePaths.reorderForest(dynamicForest);

			// remove the node from its tree but store the old position.
			std::vector<node> curChildren(dynamicForest.children(nodeToMove));
			node curParent = dynamicForest.parent(nodeToMove);
			count curEdits = G.degree(nodeToMove);

			std::fill(depth.begin(), depth.end(), 0);
			dynamicForest.dfsFrom(none, [&](node c) {
				if (c != none && dynamicForest.parent(c) != none) {
					depth[c] = depth[dynamicForest.parent(c)] + 1;
				}
			}, [](node){});
			dynamicForest.dfsFrom(nodeToMove, [&](node c) {
				--depth[c];
				if (c != nodeToMove) {
					curEdits += 1 - 2 * marker[c];
				}
			}, [](node){});

			for (node p = dynamicForest.parent(nodeToMove); p != none; p = dynamicForest.parent(p)) {
				curEdits += 1 - 2 * marker[p];
			}
			
			
			dynamicForest.isolate(nodeToMove);
			

			depth[nodeToMove] = 0;

			G.forEdgesOf(nodeToMove, [&](node v) {
				neighbors.push_back(v);
			});

			bucketQueue.fill(neighbors, depth);
			
			count level = 0;
			count bestParent = none;
			count rootMaxGain = 0, rootEdits = 0;

			auto processNode = [&](node u) {
				TRACE("Processing node ", u, " of depth ", depth[u], " (node to move: ", nodeToMove, ")");
				TRACE("Parent: ", dynamicForest.parent(u), ", children: ", dynamicForest.children(u));
				assert(u != nodeToMove);

				if (!nodeTouched[u]) {
					nodeTouched[u] = true;
					touchedNodes.emplace_back(u);
					assert(marker[u]); // only marked neighbors may be processed without having been touched before
				}

				count sumPositiveEdits = editDifference[u];

				assert(editDifference[u] != none);

				editDifference[u] += marker[u];
				editDifference[u] -= 1 - marker[u]; // if (marker[u]) { ++editDifference[u]; } else { --editDifference[u]; }

				TRACE("Edit difference before descending: ", editDifference[u]);

				assert(!marker[u] || editDifference[u] > 0);

				if (editDifference[u] != none) {
					assert(lastVisitedDFSNode[u] == u);

					node c = dynamicForest.nextDFSNodeOnEnter(u, u);

					while (c != u) {
						assert(depth[c] > level);

						if (!nodeTouched[c] || editDifference[c] == none) {
							--editDifference[u];

							// advance to the next starting point for the DFS search.
							c = lastVisitedDFSNode[c];

							if (editDifference[u] == none) {
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

				TRACE("Edit difference after descending: ", editDifference[u]);

				if (sumPositiveEdits > maxGain[u] || maxGain[u] == 0) {
					maxGain[u] = sumPositiveEdits;
					bestParentBelow[u] = u;
				}

				assert(maxGain[u] != none);

				maxGain[u] += marker[u];

				if (maxGain[u] > 0) {
					maxGain[u] -= 1 - marker[u];
				}

				TRACE("Maximum gain at ", u, ": ", maxGain[u]);

				if (maxGain[u] > 0 || (editDifference[u] != none && editDifference[u] != 0)) {
					node p = dynamicForest.parent(u);

					if (p != none) {
						if (!nodeTouched[p]) {
							nodeTouched[p] = true;
							touchedNodes.push_back(p);
							if(!marker[p]){
								bucketQueue.insertParent(p);
							}
						}

						if (editDifference[u] != none) {
							assert(editDifference[u] <= maxGain[u]);
							editDifference[p] += editDifference[u];
						}

						if (maxGain[u] > maxGain[p]) {
							maxGain[p] = maxGain[u];
							bestParentBelow[p] = bestParentBelow[u];
						}
					} else {
						if (maxGain[u] > rootMaxGain) {
							rootMaxGain = maxGain[u];
							bestParent = bestParentBelow[u];
						}

						if (editDifference[u] != none) {
							rootEdits += editDifference[u];
						}
					}
				}

				if (dynamicForest.children(u).empty()) { assert(editDifference[u] == 1); }
			};

		
			while(!bucketQueue.empty()){
				node u = bucketQueue.next();
				level = depth[u];
				processNode(u);
			}

			count bestEdits = G.degree(nodeToMove) - rootMaxGain;

			if (rootEdits > rootMaxGain) {
				bestParent = none;
				bestEdits = G.degree(nodeToMove) - rootEdits;
			}

			std::vector<node> bestChildren;

			for (node u : touchedNodes) {
				if (u != nodeToMove && dynamicForest.parent(u) == bestParent && editDifference[u] != none && editDifference[u] > 0) {
					bestChildren.push_back(u);
				}
			}

			std::vector<count> missingBelow, missingAbove, existingBelow, existingAbove;

			bool countExactEdits = moveSubtrees;
#ifndef NDEBUG
			countExactEdits = true;
#endif

			if (countExactEdits) {
				missingBelow.resize(G.upperNodeIdBound(), 0);
				missingAbove.resize(G.upperNodeIdBound(), 0);
				existingBelow.resize(G.upperNodeIdBound(), 0);
				existingAbove.resize(G.upperNodeIdBound(), 0);

				dynamicForest.forChildrenOf(none, [&](node r) {
					dynamicForest.dfsFrom(r,
					[&](node u) {
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
						}
					});
				});

				assert(missingBelow[nodeToMove] == 0);
				assert(existingBelow[nodeToMove] == 0);

				for (node c : curChildren) {
					missingBelow[nodeToMove] += missingBelow[c];
					existingBelow[nodeToMove] += existingBelow[c];
				}

				if (curParent != none) {
					missingAbove[nodeToMove] = missingAbove[curParent];
					existingAbove[nodeToMove] = existingAbove[curParent];
				}
			}

#ifndef NDEBUG
			assert(curEdits == G.degree(nodeToMove) - existingAbove[nodeToMove] - existingBelow[nodeToMove] + missingAbove[nodeToMove] + missingBelow[nodeToMove]);

			count minEdits = curEdits;
			std::vector<node> minChildren;
			node minParent = curParent;
			G.forNodes([&](node u) {
				if (u == nodeToMove) return;
				if (existingBelow[u] >= missingBelow[u] || (editDifference[u] > 0 && editDifference[u] != none)) {
					assert(editDifference[u] == existingBelow[u] - missingBelow[u]);
				} else if (nodeTouched[u]) {
					assert(editDifference[u] == none);
				}
			});

			G.forNodes([&](node u) {
				if (dynamicForest.children(u).empty() && marker[u]) {
					assert(editDifference[u] == 1);
				}
			});

			auto tryEditBelow = [&](node p) {
				if (p == nodeToMove) return;

				count edits = G.degree(nodeToMove);
				if (p != none) {
					edits += missingAbove[p];
					edits -= existingAbove[p];
				}

				std::vector<node> children;
				dynamicForest.forChildrenOf(p, [&](node c) {
					if (c == nodeToMove) return;
					if (existingBelow[c] > missingBelow[c]) { // TODO try >= (more children...)
						if (dynamicForest.children(c).empty() && marker[c]) {
							assert(editDifference[c] == 1);
						}
						assert(editDifference[c] == existingBelow[c] - missingBelow[c]);

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

			assert(minEdits == bestEdits);

			count editDifferenceControl = G.degree(nodeToMove);
			if (bestParent != none) {
				editDifferenceControl -= (existingAbove[bestParent] - missingAbove[bestParent]);
			}

			for (node u : bestChildren) {
				editDifferenceControl -= (existingBelow[u] - missingBelow[u]);
			}
			assert(minEdits == editDifferenceControl);

			TRACE("Current edits: ", curEdits, " (with parent ", curParent, " and current children ", curChildren, "), minimum edits: ", minEdits);
			TRACE("Quadratic algorithm wants to have new parent ", minParent, " and new children ", minChildren);
			TRACE("Linear algorithm wants to have new parent ", bestParent, " and new children ", bestChildren);
#endif
			bool moveWithSubtree = false;

			// calculate the number of saved edits as comparing the absolute number of edits doesn't make sense
			count savedEdits = curEdits - bestEdits;

			// cleanup for linear move
			for (node u : touchedNodes) {
				lastVisitedDFSNode[u] = u;
				maxGain[u] = 0;
				editDifference[u] = 0;
				nodeTouched[u] = false;
				bestParentBelow[u] = none;
			}

			neighbors.clear();
			touchedNodes.clear();

			G.forEdgesOf(nodeToMove, [&](node v) {
				marker[v] = false;
			});

			if (moveSubtrees) {
				
				dynamicForest.setParent(nodeToMove, curParent);
				for (node c : curChildren) {
					dynamicForest.setParent(c, nodeToMove);
				}

				count subtreeSize = 0;
				dynamicForest.dfsFrom(nodeToMove, [&](node d) {
					marker[d] = true;
					++subtreeSize;
				}, [](node) {});

				count subtreeExtDegree = 0;
				dynamicForest.dfsFrom(nodeToMove, [&](node d) {
					G.forNeighborsOf(d, [&](node v) {
						if (!marker[v]) {
							++numNeighbors[v];
							++subtreeExtDegree;
						}
					});
				}, [](node) {});

				dynamicForest.forChildrenOf(none, [&](node r) {
					dynamicForest.dfsFrom(r,
					[&](node u) {
						if (!marker[u]) {
							missingAbove[u] = subtreeSize - numNeighbors[u];
							existingAbove[u] = numNeighbors[u];
							node p = dynamicForest.parent(u);
							if (p != none) {
								missingAbove[u] += missingAbove[p];
								existingAbove[u] += existingAbove[p];
							}
						}
					},
					[](node) {});
				});

				// virtually remove the subtree of u from the forest concerning the missing/existingBelow-counters
				for (node u = curParent; u != none; u = dynamicForest.parent(u)) {
					existingBelow[u] -= existingBelow[nodeToMove];
					missingBelow[u] -= missingBelow[nodeToMove];
				}

				// calculate how many edits the whole subtree currently needs
				count curSubtreeEdits = subtreeExtDegree;
				if (curParent != none) { // FIXME here we ignore edits inside the tree as they do not change. Is this okay?
					curSubtreeEdits += missingAbove[curParent];
					curSubtreeEdits -= existingAbove[curParent];
				}

				auto trySubtreeEditBelow = [&](node p) {
					if (p != none && marker[p]) return;

					count edits = subtreeExtDegree;
					if (p != none) {
						edits += missingAbove[p];
						edits -= existingAbove[p];
					}

					std::vector<node> children;
					dynamicForest.forChildrenOf(p, [&](node c) {
						if (marker[c]) return;
						if (existingBelow[c] >= missingBelow[c]) { // TODO try >= (more children...)
							children.emplace_back(c);
							edits -= existingBelow[c] - missingBelow[c];
						}
					});

					if (edits < curSubtreeEdits && savedEdits < curSubtreeEdits - edits) {
						bestEdits = edits;
						bestChildren = std::move(children);
						bestParent = p;
						moveWithSubtree = true;
						savedEdits = curSubtreeEdits - edits;
					}

				};

				G.forNodes(trySubtreeEditBelow);
				trySubtreeEditBelow(none);

				dynamicForest.dfsFrom(nodeToMove, [&](node d) {
					marker[d] = false;
					G.forNeighborsOf(d, [&](node v) {
						numNeighbors[v] = 0;
					});
				}, [](node) {});

				TRACE("After subtree moving, ", savedEdits, " edits will be saved");
				TRACE("After subtree moving (quadratic) algorithm wants to have new parent ", bestParent, " and new children ", bestChildren);
			}


			if (savedEdits > 0) {
				if(curParent != none){
					simplePaths.splitPathAfter(curParent);
				}
				if(bestParent != none) {
					simplePaths.splitPathAfter(bestParent);
				}
				if (!moveWithSubtree) {
					dynamicForest.isolate(nodeToMove);
					
					//isolate from simple path
					simplePaths.splitPathAfter(nodeToMove);
					std::vector<node> leftBack = dynamicForest.children(curParent);
					if(leftBack.size() == 1 && curParent != none && curParent != bestParent){
						INFO("Union old paths");
						simplePaths.unionPathsOf(leftBack[0], curParent);
					}
				}
				
				count childNumber = dynamicForest.children(bestParent).size();
				//all children are adopted (or best parent was leaf before)
				if(bestParent != none && childNumber == bestChildren.size()){
					INFO("Union with parent");
				  simplePaths.unionPathsOf(nodeToMove, bestParent);
				}

				//exactly one child is adopted
				if(bestChildren.size() == 1 && !moveWithSubtree){
					INFO("Union with child");
				  simplePaths.unionPathsOf(bestChildren[0], nodeToMove);
				}

				dynamicForest.setParent(nodeToMove, bestParent);
				for (node c : bestChildren) {
					dynamicForest.setParent(c, nodeToMove);
				}

				hasMoved = true;
				numEdits -= savedEdits;

#ifndef NDEBUG
				forest = dynamicForest.toGraph();
				if(numEdits!=countNumberOfEdits()){
					INFO("Num edits ", numEdits);
					INFO("Counted ", countNumberOfEdits());
				}
				assert(numEdits == countNumberOfEdits());
#endif
			} else if (!moveSubtrees) {

				dynamicForest.setParent(nodeToMove, curParent);
			
				for (node c : curChildren) {
					dynamicForest.setParent(c, nodeToMove);
				}
			}

			dynamicForest.dfsFrom(nodeToMove, [&](node c) {
				if (dynamicForest.parent(c) != none) {
					depth[c] = depth[dynamicForest.parent(c)] + 1;
				} else {
					depth[c] = 0;
				}
			}, [](node){});
			
		if(savedEdits > 0){
			INFO("Moved node ", nodeToMove, " from parent ", curParent, " to ", bestParent);
			if(moveWithSubtree){
				INFO("Adopted children ", bestChildren, " kept children ", curChildren);
			} else {
				INFO("Adopted children ", bestChildren, " discarded children ", curChildren);
			}
		} else {
			INFO("Do not move ", nodeToMove);
		}

		
		INFO(simplePaths.printPaths());
		INFO("*****************************************************************");
			
		SimplePathState treePaths(dynamicForest, G.upperNodeIdBound());
		assert(simplePaths.equals(treePaths));
		//simplePaths = treePaths;
		});

		usedIterations = i+1;
	}

	forest = dynamicForest.toGraph();


	if(numEdits!=countNumberOfEdits()){
		INFO("Num edits ", numEdits);
		INFO("Counted ", countNumberOfEdits());
	}
	assert(numEdits == countNumberOfEdits());
}

NetworKit::count NetworKit::QuasiThresholdEditingLocalMover::countNumberOfEdits() const {
	DynamicForest dynamicForest(forest);

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
}


std::vector< NetworKit::node > NetworKit::QuasiThresholdEditingLocalMover::getParents() const {
	std::vector<node> parents(G.upperNodeIdBound());

	G.forNodes([&](node u) {
		node p = none;
		forest.forNeighborsOf(u, [&](node v) {
			p = v;
		});

		parents[u] = p;
	});

	return parents;
}

NetworKit::Cover NetworKit::QuasiThresholdEditingLocalMover::getCover(index mergeDepth) const {
	Cover c(G.upperNodeIdBound());

	DynamicForest dynamicForest(forest);

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
}



NetworKit::count NetworKit::QuasiThresholdEditingLocalMover::getNumberOfEdits() const {
	return numEdits;
}

NetworKit::Graph NetworKit::QuasiThresholdEditingLocalMover::getQuasiThresholdGraph() const {
	TreeReachabilityGraphGenerator gen(forest);
	gen.run();
	return gen.getGraph();
}

NetworKit::count NetworKit::QuasiThresholdEditingLocalMover::getUsedIterations() const {
	return usedIterations;
}
