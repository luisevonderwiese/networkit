/*
 * JaccardIndex.hpp
 *
 *  Created on: 23.03.2015
 *      Author: Kolja Esders
 */

#ifndef NETWORKIT_LINKPREDICTION_JACCARD_INDEX_HPP_
#define NETWORKIT_LINKPREDICTION_JACCARD_INDEX_HPP_

#include <networkit/linkprediction/LinkPredictor.hpp>

namespace NetworKit {

/**
 * @ingroup linkprediction
 *
 * Implementation of the Jaccard index which normalizes the Common Neighbors Index.
 * This is done through dividing the number of common neighbors by the number of nodes
 * in the neighboorhood-union.
 */
class JaccardIndex final : public LinkPredictor {
private:
  /**
   * Returns the Jaccard index for the given node-pair (@a u, @a v).
   * @param u First node
   * @param v Second node
   * @return the Jaccard index for the given node-pair (@a u, @a v)
   */
  double runImpl(node u, node v) override;

public:
  using LinkPredictor::LinkPredictor;
  
};

} // namespace NetworKit

#endif // NETWORKIT_LINKPREDICTION_JACCARD_INDEX_HPP_
