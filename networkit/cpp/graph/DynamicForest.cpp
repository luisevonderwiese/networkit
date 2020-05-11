/*
 *
 */

#include <networkit/graph/DynamicForest.hpp>
#include <set>

namespace NetworKit {

DynamicForest::DynamicForest(const NetworKit::Graph &G) :
path_membership(G.upperNodeIdBound(), none),
path_pos(G.upperNodeIdBound(), 0),
freeList(),
paths(G.upperNodeIdBound(), SimplePath()) {
	//at first every node is in its own path
	std::iota(path_membership.begin(), path_membership.end(), 0);
	
	//build up parent/child relations
	G.forNodes([&](node u) {
		paths[path(u)].pathNodes.push_back(u);
		if (G.degreeOut(u) == 0) {
			paths[path(u)].posInParent = roots.size();
			roots.push_back(path(u));
			paths[path(u)].depth = 0;
		}
		G.forEdgesOf(u, [&](node v) {
			paths[path(u)].parent = path(v);
			paths[path(u)].posInParent = paths[path(v)].childPaths.size();
			paths[path(v)].childPaths.push_back(path(u));
		});
	});
	
	//union nodes in simple paths by dfs
	pathDfsFrom(none, [&](pid subtreePath) {
		if(subtreePath != none){
			pid p = paths[subtreePath].parent;
			if(p != none && paths[p].childPaths.size() == 1){
				unionPaths(p, subtreePath);
			}
		}
	}, [](pid){});
	updateDepthInSubtree(none);
	assert(pathsValid());
	TRACE("Dynamic Forest constructed");
}

std::vector<node> DynamicForest::children(node u) const {
	std::vector<node> result;

	forChildrenOf(u, [&](node c) {
		result.emplace_back(c);
	});

	return result;
}

node DynamicForest::parent(node u) const { 
	if(u == none){
		return none;
	} else if(isUpperEnd(u)){
		pid p = paths[path(u)].parent;
		return (p == none) ? none : paths[p].lowerEnd();
	} else {
		return previousNodeInPath(u);
	} 
}

count DynamicForest::depth(node u) const { 
	if(u ==  none){
		return none;
	} else {
		return paths[path(u)].depth + paths[path(u)].length() - 1 - path_pos[u];
	}
}


void DynamicForest::updateDepthInSubtree(pid start){
	if(start != none){
		pid p = paths[start].parent;
		if(p != none){
			paths[start].depth = paths[p].depth + paths[p].length();
 		} else {
			paths[start].depth = 0;
		}
	}
	pathDfsFrom(start, [&](pid sp) {
		if (sp != none){
			pid p = paths[sp].parent;
			if(p != none){
				paths[sp].depth = paths[p].depth + paths[p].length();
			} else {
				paths[sp].depth = 0;
			}
		}  
	}, [](pid){});
}


void DynamicForest::setParentPath(pid s, pid p){
	pid oldP = paths[s].parent;
	if (oldP == p || s == p) return;
	index oldPos = paths[s].posInParent;
	//tidy up at old position
	if (oldP != none) {
		paths[oldP].childPaths[oldPos] = paths[oldP].childPaths.back();
		paths[oldP].childPaths.pop_back();
		paths[paths[oldP].childPaths[oldPos]].posInParent = oldPos;
	} else {
		roots[oldPos] = roots.back();
		roots.pop_back();
		paths[roots[oldPos]].posInParent = oldPos;
	}

	//place at new position
	paths[s].parent = p;
	if (p == none) {
		paths[s].posInParent = roots.size();
		roots.push_back(s);
	} else {
		paths[s].posInParent = paths[p].childPaths.size();
		paths[p].childPaths.push_back(s);
	}
}


void DynamicForest::isolate(node u) {
	node oldParent = parent(u);
	if(paths[path(u)].length() == 1){
		TRACE("Isolate ", u, " as path");
		isolatePath(path(u));
	} else {
		TRACE("Isolate ", u, " from path");
		isolateNode(u);
	}
	assert(pathsValid());
	
}

//isolate complete simple path
void DynamicForest::isolatePath(pid sp){
	std::vector<pid> oldChildren = paths[sp].childPaths;	
	assert(oldChildren.size() != 1);
	pid oldParent = paths[sp].parent;
	count siblings = paths[oldParent].childPaths.size() -1;
	assert(siblings >= 0);
	setParentPath(sp, none);
	//union paths if exactly one sibling is left back
	if(oldChildren.size() == 0 && siblings == 1){
		assert(paths[oldParent].childPaths.size() == 1);
		pid child = paths[oldParent].childPaths[0];
		unionPaths(oldParent, child);
		updateDepthInSubtree(child);
	} else {
		for(pid child : oldChildren){
			setParentPath(child, oldParent);
			updateDepthInSubtree(child);
		}
	}
	updateDepthInSubtree(sp);
	TRACE(oldChildren);
	
#ifndef NDEBUG
	for(pid i = 0; i < paths.size(); i++){
		assert(paths[i].parent != sp);
		for(pid c : paths[i].childPaths){
			assert(c != sp);
		}
	}
#endif
}

//isolate a node from a path of size >= 2
void DynamicForest::isolateNode(node u){
	pid sp = path(u);
	index oldPos = path_pos[u];
	assert(paths[sp].length() >= 2);
	//shift nodes
	for(index i = oldPos + 1; i < paths[sp].length(); i++){
		node nodeToMove = paths[sp].pathNodes[i];
		paths[sp].pathNodes[i-1] = nodeToMove;
		path_pos[nodeToMove] = i-1;
	}
	paths[sp].pathNodes.pop_back();
	//create new isolated path
	pid np = newPath();
	paths[np].posInParent = roots.size();
	roots.push_back(np);
	addToPath(u, np);
	updateDepthInSubtree(sp);
}


void DynamicForest::moveUpNeighbor(node neighbor, node referenceNode) {
	pid sp = path(neighbor);
	if(paths[sp].length() > 1){
		TRACE("Move up ", neighbor);
		//update referenceNode if necessary
		if(paths[sp].referenceNode != referenceNode){
			paths[sp].referenceNode = referenceNode;
			paths[sp].neighborCount = 0;
		}
		if(paths[sp].neighborCount >= paths[sp].length()) return; //already all neighbors considered
		index oldPos = path_pos[neighbor];
		index neighborPos = paths[sp].length() - 1 - paths[sp].neighborCount;
		if(oldPos > neighborPos) return; //neighbor already considered
		paths[sp].neighborCount++;
		if(oldPos ==  neighborPos) return; //neighbor was not considered but is at right position
		node firstNonNeighbor = paths[sp].pathNodes[neighborPos];
		swapNodesWithinPath(firstNonNeighbor, neighbor);
		}
	assert(pathsValid());		
}


void DynamicForest::swapNodesWithinPath(node u, node v){
	pid sp = path(u);
	assert(path(v) == sp);
	if(u == v){
		return;
	}
	index oldPos = path_pos[u];
	path_pos[u] = path_pos[v];
	paths[sp].pathNodes[path_pos[v]] = u;
	path_pos[v] = oldPos;
	paths[sp].pathNodes[oldPos] = v;
}

void DynamicForest::addToPath(node u, pid newId){
	path_membership[u] = newId;
	path_pos[u] = paths[newId].length();
	paths[newId].pathNodes.push_back(u);
}

void DynamicForest::splitPath(pid sp, index splitPos){
	if(paths[sp].length() <= 1 || splitPos == 0) return; //nothing to split
	assert(splitPos < paths[sp].length());
	pid oldParent = paths[sp].parent;
	index oldPosInParent = paths[sp].posInParent;
	count oldDepth = paths[sp].depth;
	
	pid np = newPath();
	//move upper nodes to new path
	for(int i = splitPos; i < paths[sp].length(); i++){
		addToPath(paths[sp].pathNodes[i], np);
	}
	paths[sp].pathNodes.erase(paths[sp].pathNodes.begin() + splitPos, paths[sp].pathNodes.end());
	//update tree structure
	paths[sp].parent = np;
	paths[sp].posInParent = 0;
	paths[np].parent = oldParent;
	paths[np].posInParent = oldPosInParent;
	if(oldParent != none){
		paths[oldParent].childPaths[oldPosInParent] = np;
	} else {
		roots[oldPosInParent] = np;
	}
	paths[np].childPaths.push_back(sp);
	paths[np].depth = oldDepth;
	paths[sp].depth = oldDepth + paths[np].length();
	//updateDepthInSubtree(np);
	assert(parent(paths[sp].upperEnd())==paths[np].lowerEnd());
	assert(children(paths[np].lowerEnd()).size() == 1);
	assert(children(paths[np].lowerEnd())[0]==paths[sp].upperEnd());
	
}

void DynamicForest::unionPaths(pid upperPath, pid lowerPath){
	if(upperPath == lowerPath){
		return;
	}
	//TRACE("Union upper path ", upperPath, " with above path ", lowerPath);
	assert(paths[upperPath].childPaths.size() == 1);
	assert(paths[upperPath].childPaths[0] == lowerPath);
	
	pid upperParent = paths[upperPath].parent;
	pid upperPos = paths[upperPath].posInParent;
	
	//update tree structure
	paths[upperPath].childPaths.pop_back();
	paths[lowerPath].parent = upperParent;
	paths[lowerPath].posInParent = upperPos;
	if(upperParent != none){
		paths[upperParent].childPaths[upperPos] = lowerPath;
	} else {
		roots[upperPos] = lowerPath;
	}
	//move nodes of upper path to lower path
	count l = paths[upperPath].length();
	for(count i = 0; i < l; i++){
		addToPath(paths[upperPath].pathNodes[i], lowerPath);
	}
	paths[upperPath].pathNodes.clear();
	deletePath(upperPath);
#ifndef NDEBUG
	if(paths[lowerPath].parent != none){
		assert(paths[paths[lowerPath].parent].childPaths[upperPos] == lowerPath);
	} else {
		assert(roots[upperPos] ==  lowerPath);
	}
#endif
}


void DynamicForest::moveToPosition(node u, node p, const std::vector<node> &adoptedChildren){
	//check that the node is isolated
	pid parentPath = path(p);
	pid oldPath = path(u);
#ifndef NDEBUG
	assert(paths[oldPath].parent == none);
	assert(parent(u) == none);
	assert(childCount(u) == 0);
	assert(paths[path(u)].length() == 1);
	//check that all children are adopted
	if(p != none){
		std::vector<node> oldChildren = children(p);
		TRACE("Move ", u, " below parent ", p, " adopting children ", adoptedChildren, " out of ", oldChildren);
		for(node c : adoptedChildren){
			assert(std::find(oldChildren.begin(), oldChildren.end(), c) != oldChildren.end());
		}
	} else {
		TRACE("Make ", u, " root adopting children ", adoptedChildren);
		for(node c : adoptedChildren){
			assert(std::find(roots.begin(), roots.end(), path(c)) != roots.end());
		}
	}
#endif
	//if all children are adopted, insert after parent
	if (adoptedChildren.size() == childCount(p)){
		//shift nodes to place the new node
		index parentPathPos = path_pos[p];
		node temp = paths[parentPath].pathNodes.back();
		path_pos[temp] = paths[parentPath].length();
		paths[parentPath].pathNodes.push_back(temp);
		for(int i = paths[parentPath].length() - 1; i > parentPathPos; i--){
			temp = paths[parentPath].pathNodes[i-1];
			path_pos[temp] = i;
			paths[parentPath].pathNodes[i] = temp;
		}
		path_pos[u] = parentPathPos;
		paths[parentPath].pathNodes[parentPathPos] = u;
		
		path_membership[u] = parentPath;
		
		//update tree structure
		index oldTreePos = paths[oldPath].posInParent;
		roots[oldTreePos] = roots.back();
		roots.pop_back();
		paths[roots[oldTreePos]].posInParent = oldTreePos;

		paths[oldPath].pathNodes.pop_back();
		deletePath(oldPath);
	} else {
		//if at least one child is not adopted, parent needs to be lower end
		if(p != none && !isLowerEnd(p)){
			splitPath(parentPath, path_pos[p]);
			parentPath = path(p);
		}
		//if exactly one child is adopted, node can just be added to that path
		if(adoptedChildren.size() == 1){
			//update Tree structure
			index oldTreePos = paths[oldPath].posInParent;
			roots[oldTreePos] = roots.back();
			roots.pop_back();
			paths[roots[oldTreePos]].posInParent = oldTreePos;
			
			paths[oldPath].pathNodes.pop_back();
			deletePath(oldPath);
			
			addToPath(u, path(adoptedChildren[0]));
		//otherwise, insert in simple-path tree structure
		} else {
			setParentPath(oldPath, parentPath);
			for(node child : adoptedChildren){
				setParentPath(path(child), path(u));
			}
		}
	}
	updateDepthInSubtree(path(u));
	assert(pathsValid());

}


bool DynamicForest::pathsValid(){
	
	//check that parent/child relations for paths are valid
	for(pid sp = 0; sp < paths.size(); sp++){
		std::vector<pid> cps = paths[sp].childPaths;
		for(index i = 0; i < cps.size(); i++){
			pid child =  cps[i];
			assert(paths[child].parent == sp);
			assert(paths[child].posInParent == i);
		}
	}
	for(index i = 0; i < roots.size(); i++){
		pid rootPath = roots[i];
		assert(paths[rootPath].parent == none);
		assert(paths[rootPath].posInParent == i);
	}
	
	for(node u = 0; u < path_membership.size(); u++){
		std::vector<node> childNodes = children(u);
		assert(childNodes.size() == childCount(u));
		//check that parent/child realtionships for nodes are proper
		for(index i = 0; i < childCount(u); i++){
			node c = childNodes[i];
			assert(u != c);
			if(i > 0){
				assert(path(u) != path(c));
			}
			assert(posInParent(c) == i);
			assert(parent(c) == u);
		}
		//check that  path_membership and positions for nodes are proper
		pid sp = path(u);
		assert(paths[sp].pathNodes[path_pos[u]] == u);
		for(index i = 0; i < paths[sp].pathNodes.size(); i++){
			node v = paths[sp].pathNodes[i];
			assert(path_pos[v] == i);
			assert(path(v) == sp);
		}
		std::vector<pid> cps = paths[sp].childPaths;
		for(pid i = 0; i < paths.size(); i++){
			if(paths[i].parent == sp){
				assert(std::find(cps.begin(), cps.end(), i) != cps.end());
			}
		}
	}
	
	//check that depth is proper for paths
	pathDfsFrom(none, [&](pid sp) {
		if (sp != none){
			pid p = paths[sp].parent;
			if(p != none){
				if(paths[sp].depth != paths[p].depth + paths[p].length()){
					TRACE(paths[sp].pathNodes);
				}
				assert(paths[sp].depth == paths[p].depth + paths[p].length());
			} else {
				if(paths[sp].depth != 0){
					TRACE(paths[sp].pathNodes);
				}
				assert(paths[sp].depth == 0);
			}
		}  
	}, [](pid){});
	
	//check that depth is proper for nodes
	dfsFrom(none, [&](node c) {
			if (c != none && parent(c) != none) {
				assert(depth(c) == depth(parent(c)) + 1);
				if(childCount(c) == 1){
					assert(path_membership[c] == path_membership[children(c)[0]]);
				}
			} 
		}, [](node){});

	//check that free list is proper
	for(pid freePlace : freeList){
		assert(paths[freePlace].parent == none);
		assert(paths[freePlace].referenceNode == none);
		assert(paths[freePlace].pathNodes.size() == 0);
		assert(paths[freePlace].childPaths.size() == 0);
		assert(paths[freePlace].neighborCount == 0);
		assert(paths[freePlace].depth == 0);
		assert(paths[freePlace].posInParent == 0);
	}
	return 1;
}




std::string DynamicForest::printPaths(){
	std::stringstream ss;
	for(node u = 0; u < path_membership.size(); u++){
		ss << "{" << u << " ";
		ss << "[";
		std::vector<node> pNodes = paths[path(u)].pathNodes;
		for(node u : pNodes){
			ss << u << " ";
		}
		ss << "]";
		if(path_pos[u] != none){
			ss << " pos " << path_pos[u];
		}
		ss << "} ";
	}
	return ss.str();
}


Graph DynamicForest::toGraph() const {
	Graph result(path_membership.size(), false, true);

	for (pid r : roots) {
		dfsFrom(paths[r].upperEnd(), [](node) {}, [&](node u) {
			if (parent(u) != none) {
				result.addEdge(u, parent(u));
			}
		});
	}

	return result;
}


//superfluous?
pid DynamicForest::path(node u) const{
	if(u == none){
		return none;
	} else {
		assert(u < path_membership.size());
		return path_membership[u];
	}
}


bool DynamicForest::isUpperEnd(node u) const{
	return (path_pos[u] == paths[path(u)].length() - 1);
}
bool DynamicForest::isLowerEnd(node u) const{
	return (path_pos[u] == 0);
}

node DynamicForest::nextNodeInPath(node u) const{
	if(isLowerEnd(u)){
		return none;
	} else {
		return paths[path(u)].pathNodes[path_pos[u] - 1];
	}
}

node DynamicForest::previousNodeInPath(node u) const{
	if(isUpperEnd(u)){
		return none;
	} else {
		return paths[path(u)].pathNodes[path_pos[u] + 1];
	}
}

void DynamicForest::deletePath(pid i){
	//check that path got isolated from tree structure
#ifndef NDEBUG
	assert(i != none);
	assert(paths[i].childPaths.size() == 0);
	for(pid sp = 0; sp < paths.size(); sp++){
		assert(paths[sp].parent != i);
		for(pid c : paths[sp].childPaths){
			assert(c != i);
		}
	}
	assert(std::find(roots.begin(), roots.end(), i) == roots.end());
#endif
	paths[i].reset();
	freeList.push_back(i);
}

pid DynamicForest::newPath(){
	assert(!freeList.empty());
	pid freePlace = freeList.back();
	freeList.pop_back();
	return freePlace;
}

count DynamicForest::childCount (node u) const{
	if(u == none){
		return roots.size();
	}
	if(!isLowerEnd(u)){
		return 1;
	} else {
		return paths[path(u)].childPaths.size();
	}
}

index NetworKit::DynamicForest::posInParent (node u) const{
	if(u == none){
		return none;
	} else if(!isUpperEnd(u)){
		return 0;
	} else {
		return paths[path(u)].posInParent;
	}
}

} //namespace NetworKit
