import scala.collection.BitSet
import scala.collection.mutable.{Buffer, Map => MMap, Set => MSet, SortedSet => MSortedSet}

import TypeAliases._

object TypeAliases {
  type NodeT = Int
  type PathT = Seq[NodeT]
  type DistanceT = Double
}

/**
  * Travelling salesman problem tomfoolery.
  *   Nodes are represented by integers [0,N).
  *   Edges are represented by a distance fn.
  */
case class Tsp(N: Int, d: (NodeT, NodeT) => DistanceT) {

  def normalised = Tsp(N, MetricUtils.normalise(N, d))

  def denormalised = Tsp(N, MetricUtils.denormalise(N, d))

  def edges(path: PathT): Seq[(NodeT, NodeT)] = path.zip(path.tail)

  def length(path: PathT): DistanceT = edges(path).map { case (n1, n2) => d(n1, n2) }.sum

  /**
    *  Generate all Hamiltonian cycles, starting and ending at node 0
    */
  def hamCycles: Iterator[PathT] = {
    (1 to N-1).permutations.map { path => Seq(0) ++ path ++ Seq(0) }
  }

  def avgHamCycle: DistanceT = hamCycles.map(length).sum / hamCycles.size

  /**
    * Find the shortest cycle by brute force.
    */
  def bruteMinHamCycle: PathT = hamCycles.minBy(length)

  /**
    *  Greedy cycle starting at the given node
    */
  def greedyHamCycle(n0: NodeT = 0): PathT = {
    var i = n0
    var nodesLeft = (0 to N-1).toSet - i
    var path = Seq(i)
    while(nodesLeft.nonEmpty) {
      // Shortest next edge
      val j = nodesLeft.minBy { n => d(i, n) }
      i = j
      nodesLeft = nodesLeft - i
      path = path :+ i
    }
    // Complete the cycle
    path ++ Seq(n0)
  }

  /**
    *  Best greedy cycle starting at any node
    */
  def bestGreedyHamCycle: PathT = {
    (0 to N-1).map { n => greedyHamCycle(n) }.minBy(length)
  }

  /**
    * Standard DP approach to TSP.
    * Iteration 0 starts with all edges (0,j).
    * Iteration M computes the shortest path for each set of size M of internal nodes, and each end-point end-point j.
    *   This can be computed from the tableau of iteration M-1.
    * Iteration N-1 gives us the shorted paths from 0 to all i, passing through all nodes.
    * We can then trivially find the shortest cycle by adding the edge back to node 0 for all paths.
    */
  def dpMinHamCycle: PathT = {
    val dpTab0 = (1 to N-1).map { k => (Set.empty[NodeT], k) -> Seq(0, k) }.toMap

    // DP iterations - M is the size of the set of interior nodes of each path
    val dpTabN = (1 to N-2).foldLeft(dpTab0) { (dpTabM, M) =>
      (1 to N-1).map { k =>
        // Generate all combinations of nodes of length M, excluding node k
        val nodesNotK = (1 to k-1) ++ (k+1 to N-1)
        nodesNotK.combinations(M).map(_.toSet).map { comboM =>
          // Choose the best path through comboM to k by iterating over paths to the node before k
          (comboM, k) -> comboM.map { j => dpTabM(comboM-j, j) :+ k }.minBy(length)
        }
      }.flatten.toMap
    }

    // Now we have the shortest paths from 0 to any i through all (other) nodes.
    // Find the best hamilton cycle by closing the loop to 0 and finding the shortest one.
    dpTabN.values.map(_ :+ 0).minBy(length)
  }

  // All edges (i, j) excluding node 0
  def edgesNon0: Seq[PathT] = (1 to N-1).map { i => (1 to N-1).collect { case j if i != j => Seq(i, j) } }.flatten

  /**
    * Alternate DP approach to TSP.
    * Iteration 0 starts with all edges (i, j) excluding node 0.
    * Iteration M starts with all paths of length M+2, and folds matching pairs together to form paths of length M+3.
    *   e.g. 1-2-3 and 2-3-4 fold together to get 1-2-3-4. And 1-2-5 and 3-5-6 don't fold.
    * At each iteration we filter the generated paths to the shorted paths from i to k through any set of interior nodes.
    */
  def foldDpMinHamCycle: PathT = {

    N match {
      case 1 => Seq(0)
      case 2 => Seq(0, 1, 0)
      case _ => {
        // All edges (i, j) excluding node 0
        val paths0: Seq[PathT] = (1 to N-1).map { i => (1 to N-1).collect { case j if i != j => Seq(i, j) } }.flatten
        // println(s"N = $N: paths0 is $paths0")

        // DP iterations - fold paths
        val pathsN =
          if(N == 3) {
            paths0
          }
          else {
            (1 to N-3).foldLeft(paths0) { (pathsM, M) =>
              // println(s"N = $N: M = $M, pathsM = $pathsM")
              // map: tail -> set of paths with this tail
              val pathsByTail = MMap[PathT, MSet[PathT]]()
              pathsM.foreach { path =>
                val pathTail = path.tail
                pathsByTail(path.tail) = (pathsByTail.getOrElse(path.tail, MSet()) += path)
              }
              // map: (i, nodes, j) => shortest folded path from i to j through nodes
              val shortestPathMap: MMap[(NodeT, Set[NodeT], NodeT), PathT] = MMap()
              pathsM.foreach { path =>
                // println(s"N = $N: M = $M,           path = $path")
                val pathInit = path.init
                // Fold this prefix with matching suffixes from our cunningly prepared suffix map
                pathsByTail.get(pathInit).foreach { pathMatches =>
                  pathMatches.foreach { pathMatch =>
                    val first = pathMatch.head
                    val last = path.last
                    if(first != last) {
                      val key = (first, pathInit.toSet, last)
                      val foldedPath = pathMatch :+ path.last
                      val shortestPath = shortestPathMap.get(key) match {
                        case None => foldedPath
                        case Some(previousPath) =>
                          if(length(previousPath) <= length(foldedPath)) previousPath else foldedPath
                      }
                      shortestPathMap(key) = shortestPath
                    }
                  }
                }
              }
              // Extract all the shortest paths
              shortestPathMap.values.toSeq
            }
          }
        // We now have a bunch of paths of length N-1, not passing through node 0, complete the cycle to 0 and find the shortest
        pathsN.map { path => /*println(s"        final $path");*/ Seq(0) ++ path ++ Seq(0) }.minBy(length)
      }
    }
  }

  abstract class PathGenFactory {
    def getPathGen(M: Int, from0: Boolean, to0: Boolean): PathGen
  }

  abstract class CachingPathGenFactory extends PathGenFactory {
    val pathGenCache = MMap[(Int, Boolean, Boolean), PathGen]()

    def getPathGen(M: Int, from0: Boolean = false, to0: Boolean = false): PathGen = {
      pathGenCache.synchronized {
        pathGenCache.getOrElseUpdate((M, from0, to0), buildPathGen(M, from0, to0))
      }
    }

    def buildPathGen(M: Int, from0: Boolean, to0: Boolean): PathGen
  }

  class PgFactory extends CachingPathGenFactory {
    def buildPathGen(M: Int, from0: Boolean, to0: Boolean): PathGen = {
      //println(s"buildPathGen($M, $from0, $to0)")
      (M, from0, to0) match {
        case (2, false, false) => new EdgesNon0
        case (2, false, true) => new EdgesTo0
        case (2, true, false) => new EdgesFrom0
        case (2, true, true) => new Edge0To0

        case (_, _, _) => new RecursivePathGen(M, from0, to0, PgFactory.this)
      }
    }
  }

  class Pg2Factory extends CachingPathGenFactory {
    def buildPathGen(M: Int, from0: Boolean, to0: Boolean): PathGen = {
      //println(s"buildPathGen($M, $from0, $to0)")
      (M, from0, to0) match {
        case (2, false, false) => new EdgesNon0
        case (2, false, true) => new EdgesTo0
        case (2, true, false) => new EdgesFrom0
        case (2, true, true) => new Edge0To0

        case (_, true, true) => new RecursivePathGen2From0To0(Pg2Factory.this)
        case (_, _, _) => new RecursivePathGen(M, from0, to0, Pg2Factory.this)
      }
    }
  }

  class Pg3Factory extends CachingPathGenFactory {
    def buildPathGen(M: Int, from0: Boolean, to0: Boolean): PathGen = {
      //println(s"buildPathGen($M, $from0, $to0)")
      (M, from0, to0) match {
        case (2, false, false) => new EdgesNon0
        case (2, false, true) => new EdgesTo0
        case (2, true, false) => new EdgesFrom0
        case (2, true, true) => new Edge0To0

        case (_, true, true) => new RecursivePathGen2From0To0(Pg3Factory.this)
        case (_, _, _) => new RecursivePathGen3(M, from0, to0, Pg3Factory.this)
      }
    }
  }

  class Pg3x2Factory extends CachingPathGenFactory {
    val pg3Factory = new Pg3Factory

    def buildPathGen(M: Int, from0: Boolean, to0: Boolean): PathGen = {
      //println(s"buildPathGen($M, $from0, $to0)")
      (M, from0, to0) match {
        case (2, false, false) => new EdgesNon0
        case (2, false, true) => new EdgesTo0
        case (2, true, false) => new EdgesFrom0
        case (2, true, true) => new Edge0To0

        case (_, true, true) => new RecursivePathGen2From0To0(Pg3x2Factory.this)
        case (_, _, _) =>
          if(3 < M) {
            new RecursivePathGen3x2(M, from0, to0, Pg3x2Factory.this)
          }
          else {
            pg3Factory.buildPathGen(M, from0, to0)
          }
      }
    }
  }

  case class PathData(head: NodeT, leftInners: BitSet, rightInners: BitSet, last: NodeT, path: PathT, length: DistanceT)

  def mkPathData(path: PathT, from0: Boolean, to0: Boolean): PathData = {
    val init = path.init
    val leftInners = if(from0) init.tail else init
    val tail = path.tail
    val rightInners = if(to0) tail.init else tail
    PathData(path.head, leftInners = BitSet(leftInners: _*), rightInners = BitSet(rightInners: _*), path.last, path.toArray, length(path))
  }

  /**
    * M is the number of nodes in a path, i.e. M-1 edges.
    */
  abstract class PathGen(M: Int, from0: Boolean, to0: Boolean) {

    /**
      * @return the i'th shortest path of length M (or None if there are fewer than i paths)
      */
    def getPath(i: Int): Option[PathData]

    def dump: Unit = {
      println(s"                          N = $N M = $M from0 = $from0 to0 = $to0:")
      var i = 0
      var done = false
      while(!done) {
        getPath(i) match {
          case None =>
            done = true
          case Some(path) =>
            println(f"                                i = $i%3d len = ${length(path.path)}%.6f (${path.length}%.6f) $path")
            i = i+1
        }
      }
    }

    def dumpStats(indent: Int): Unit = {/*nothing*/}
  }

  class PathGenFromArray(M: Int, from0: Boolean, to0: Boolean, paths: Array[PathData])
      extends PathGen(M, from0, to0) {

    override def getPath(i: Int): Option[PathData] = if(i < paths.size) Some(paths(i)) else None
  }

  /**
    * Single-edge paths in increasing order of length.
    */
  class EdgesNon0 extends PathGenFromArray(M = 2, from0 = false, to0 = false, paths = edgesNon0.toArray.sortBy(length).map(mkPathData(_, from0 = false, to0 = false)))

  /**
    * Single-edge edges from 0 in increasing order of length.
    */
  class EdgesFrom0 extends PathGenFromArray(M = 2, from0 = true, to0 = false, paths = (1 to N-1).map { i => Seq(0, i) }.toArray.sortBy(length).map(mkPathData(_, from0 = true, to0 = false)))

  /**
    * Single-edge edges from 0 in increasing order of length.
    */
  class EdgesTo0 extends PathGenFromArray(M = 2, from0 = false, to0 = true, paths = (1 to N-1).map { i => Seq(i, 0) }.toArray.sortBy(length).map(mkPathData(_, from0 = false, to0 = true)))

  /**
    * Pathological case edge 0 to 0
    */
  class Edge0To0 extends PathGenFromArray(M = 2, from0 = true, to0 = true, paths = Array(Seq(0, 0)).map(mkPathData(_, from0 = true, to0 = true)))

  /**
    * Generate paths by patching together two paths of approximately half the length.
    * For the special case of the top-level PathGen, we can immediately match
    *   left & right paths by their last and head node, respectively, and the inverse
    *   of their internal nodes.
    */
  class RecursivePathGen2From0To0(factory: PathGenFactory)
      extends PathGen(M = N+1, from0 = true, to0 = true) {

    val leftPathGen = mkLeftPathGen
    val rightPathGen = mkRightPathGen
    def mkLeftPathGen = factory.getPathGen((N+1 + 2)/2, from0 = true, to0 = false)
    def mkRightPathGen = factory.getPathGen((N+1 + 1)/2, from0 = false, to0 = true)

    // map: (last-node, other non-0 nodes) -> left path index
    val leftPaths = MMap[(NodeT, BitSet), Int]()

    // map: (head-node, other non-0 nodes) -> right path index
    val rightPaths = MMap[(NodeT, BitSet), Int]()

    // Seed the left paths
    var leftDone = false
    var iLeftNext = 0
    var leftNext: PathData = leftPathGen.getPath(0).get
    val minLeftLength = leftNext.length

    // Seed the right paths
    var rightDone = false
    var iRightNext = 0
    var rightNext: PathData = rightPathGen.getPath(0).get
    val minRightLength = rightNext.length

    val allNon0NodesBitset = BitSet((1 to N-1): _*)

    // Paths pending release, ordered by path length.
    // A path is released (published) once we have looked far enough forward in both left and right
    //   subpaths to prove that there can be no shorter path.
    // Set(length, left-index, right-index)
    val pendingPaths = MSortedSet[(DistanceT, Int, Int)]()
    var minPendingLeftLength = 0.0
    var minPendingRightLength = 0.0

    // Paths already generated, indexed on the triple of (head, set of internal nodes, last).
    // Used to eliminate obviously inferior paths comprising the same two end-points,
    //   and the same interior nodes in a different (and longer path) order.
    val pathsByInteriorSet = MMap[(NodeT, BitSet, NodeT), PathT]()
    var nDups = 0

    // Paths already generated, in order of length - we typically only generate paths(0) since that is the TSP solution
    val paths = Buffer[PathData]()

    override def dumpStats(indent: Int): Unit = {
      (0 to indent).foreach { i => print("  ") }
      println(f"                                                                                   pg2 ${N+1}:0-0 #paths ${paths.size} #lefts $iLeftNext #rights $iRightNext #dups ${nDups} #pending ${pendingPaths.size}")
      // paths.foreach { pd =>
      //   (0 to indent).foreach { i => print("  ") }
      //   println(f"                                                                                         ${pd.length}%.4f ${pd.path}")
      // }
      leftPathGen.dumpStats(indent+1)
      rightPathGen.dumpStats(indent+1)
    }

    override def getPath(i: Int): Option[PathData] = {
      fillTo(i)
      //println(f"                                                                                   pg2 0to0 i = $i: #lefts $iLeftNext #rights $iRightNext #pending ${pendingPaths.size}")
      if(i < paths.size) Some(paths(i)) else None
    }

    def inverseNodeSet(nodeSet: BitSet, edgeNode: NodeT): BitSet = {
      allNon0NodesBitset -- nodeSet - edgeNode
    }

    /**
      * Generate paths up to the i'th path.
      */
    def fillTo(i: Int): Unit = {
      while(paths.size <= i && (pendingPaths.nonEmpty || !leftDone || !rightDone)) {
        doNext()
      }
    }

    def bumpLeft(): Unit = {
      iLeftNext = iLeftNext + 1
      leftPathGen.getPath(iLeftNext) match {
        case None =>
          leftDone = true
          // println(s"                                         left done after $iLeftNext subpaths")
        case Some(pathData) =>
          leftNext = pathData
          // println(f"                                         left $iLeftNext = ${pathData.path.toList} len ${pathData.length}%.4f")
      }
    }

    def bumpRight(): Unit = {
      iRightNext = iRightNext + 1
      rightPathGen.getPath(iRightNext) match {
        case None =>
          rightDone = true
          // println(f"                                                                                                         right done after $iRightNext subpaths")
        case Some(pathData) =>
          rightNext = pathData
          // println(f"                                                                                                         right $iRightNext = ${pathData.path.toList} len ${pathData.length}%.4f")
      }
    }

    def addLeft(iLeft: Int, left: PathData): Unit = {
      // Add to the left cache
      leftPaths((left.last, left.leftInners)) = iLeft

      // Is there a right match?
      rightPaths.get((left.last, inverseNodeSet(left.leftInners, left.last))) match {
        case None => /*boo :(*/
        case Some(iRight) =>
          addPendingPath(iLeft, iRight)
      }
    }

    def addRight(iRight: Int, right: PathData): Unit = {
      rightPaths((right.head, right.rightInners)) = iRight

      // Is there a left match?
      leftPaths.get((right.head, inverseNodeSet(right.rightInners, right.head))) match {
        case None => /*boo :(*/
        case Some(iLeft) =>
          addPendingPath(iLeft, iRight)
      }
    }

    def addPendingPath(iLeft: Int, iRight: Int): Unit = {
      val left = leftPathGen.getPath(iLeft).get
      val right = rightPathGen.getPath(iRight).get
      val pendingPath = (left.length + right.length, iLeft, iRight)
      // if(paths.isEmpty && pendingPaths.isEmpty) {
      //   println(f"                                                                                                    first pending path left #${iLeft} right #${iRight} #lefts ${iLeftNext} #rights ${iRightNext} - len ${pendingPath._1}%.4f ${left.path.toList} + ${right.path.toList}")
      // }
      pendingPaths += pendingPath
      // println(f"                                         added pending path len ${pendingPath._1}%.4f ${left.path.toList} + ${right.path.toList}")
      updateMinPendingLengths()
    }

    def updateMinPendingLengths(): Unit = {
      val (minLength, minILeft, minIRight) = pendingPaths.head
      val minLeft = leftPathGen.getPath(minILeft).get
      val minRight = rightPathGen.getPath(minIRight).get
      minPendingLeftLength = minLeft.length
      minPendingRightLength = minRight.length
      // println(f"                                         min(pending) is now len $minLength%.4f ${minLeft.path.toList} + ${minRight.path.toList}")
    }

    def doNextPending(): Unit = {
      val nextPath = pendingPaths.head
      pendingPaths -= nextPath
      val(length, iLeft, iRight) = nextPath
      val left = leftPathGen.getPath(iLeft).get
      val right = rightPathGen.getPath(iRight).get
      //println(f"                                                                              releasing $iLeft len ${left.length}%.4f + $iRight len ${right.length}%.4f min ($minLeftLength%.4f $minRightLength%.4f) next $iLeftNext len ${leftNext.length}%.4f $iRightNext len ${rightNext.length}%.4f")
      addPath(left, right)
      // println(f"                                         removed pending path len ${nextPath._1}%.4f ${left.path.toList} + ${right.path.toList}")

      if(pendingPaths.isEmpty) {
        // println(f"                                         pending is now empty")
      }
      else {
        updateMinPendingLengths()
      }
    }

    def addPath(left: PathData, right: PathData): Unit = {
      // Success - patch the left and right paths together
      val path = left.path ++ right.path.tail
      val inners = BitSet(path.tail.init: _*)
      val key = (path.head, inners, path.last)
      // println(f"                       released path len ${left.length + right.length}%.4f - ${left.path.toList} + ${right.path.toList}")
      // println(f"                       after #lefts $iLeftNext and #rights $iRightNext - still ${pendingPaths.size} pending")
      pathsByInteriorSet.get(key) match {
        case None =>
          // No better path through the same nodes - this is a genuine new path
          pathsByInteriorSet(key) = path
          paths += mkPathData(path, from0 = true, to0 = true)
        case Some(betterPath) =>
          // Ignore this path - we already have a better one through the same nodes
          nDups = nDups + 1
          // println(f"                       ignored - we already have len ${length(betterPath)}%.4f ${betterPath.toList}")
      }
    }

    def doNextLeft(): Unit = {
      val iLeft = iLeftNext
      val left = leftNext
      bumpLeft()
      addLeft(iLeft, left)
    }

    def doNextRight(): Unit = {
      val iRight = iRightNext
      val right = rightNext
      bumpRight()
      addRight(iRight, right)
    }

    def doNext(): Unit = {
      //// println(s"look at new pair $iLeftNext and $iRightNext")
      if(iLeftNext == 0 && iRightNext == 0) {
        // Seed with the first left and right
        doNextLeft()
        doNextRight()
      }
      else {
        // First priority is releasing a pending path
        val minPendingLength = minPendingLeftLength + minPendingRightLength
        if(pendingPaths.nonEmpty
          /*&& (leftDone || minPendingLeftLength - minLeftLength <= leftNext.length - minPendingLeftLength)
           && (rightDone || minPendingRightLength - minRightLength <= rightNext.length - minPendingRightLength)*/
           && (leftDone || minPendingLength <= leftNext.length + minRightLength)
           && (rightDone || minPendingLength <= minLeftLength + rightNext.length)
        ) {

          // println("          doing next pending")
          doNextPending()
        }
        else {
          // Move either the left or right forward by 1
          if(leftDone) {
            // println("          left done - doing right")
            doNextRight()
          }
          else if(rightDone) {
            // println("          right done - doing left")
            doNextLeft()
          }
          else {
            // println(f"         left $iLeftNext len ${leftNext.length}%.4f + min(right) $minRightLength%.4f < min(left) $minLeftLength%.4f + right $iRightNext ${rightNext.length}%.4f")
            if(leftNext.length + minRightLength < minLeftLength + rightNext.length) {
              doNextLeft()
            }
            else {
              doNextRight()
            }
          }
        }
      }
    }

  }

  /**
    * Generate paths by patching together two paths of approximately half the length.
    * For the special case of the top-level PathGen, we can immediately match
    *   left & right paths by their last and head node, respectively, and the inverse
    *   of their internal nodes.
    */
  class RecursivePathGen3(M: Int, from0: Boolean, to0: Boolean, factory: PathGenFactory)
      extends PathGen(M, from0, to0) {

    val leftPathGen = factory.getPathGen((M+2)/2, from0, to0 = false)

    val rightPathGen = factory.getPathGen((M+1)/2, from0 = false, to0)

    // leftPathsByLast(last-node) = indexes of left paths ending in last-node
    val leftPathsByLast = Array.fill(N) { Buffer[Int]() }

    // rightPathsByFirst(first-node) = indexes of right paths beginning with last-node
    val rightPathsByFirst = Array.fill(N) { Buffer[Int]() }

    // Seed the left paths
    var leftDone = false
    var iLeftNext = 0
    var leftNext: PathData = leftPathGen.getPath(0).get
    val minLeftLength = leftNext.length

    // Seed the right paths
    var rightDone = false
    var iRightNext = 0
    var rightNext: PathData = rightPathGen.getPath(0).get
    val minRightLength = rightNext.length

    val allNon0NodesBitset = BitSet((1 to N-1): _*)

    // Paths pending release, ordered by path length.
    // A path is released (published) once we have looked far enough forward in both left and right
    //   subpaths to prove that there can be no shorter path.
    // Set(length, left-index, right-index, linkNode, left-max, right-max)
    val pendingPaths = MSortedSet[(DistanceT, Int, Int, NodeT, Int, Int, Int)]()
    var minPendingLeftLength = 0.0
    var minPendingRightLength = 0.0

    // Paths already generated, indexed on the triple of (head, set of internal nodes, last).
    // Used to eliminate obviously inferior paths comprising the same two end-points,
    //   and the same interior nodes in a different (and longer path) order.
    val pathsByInteriorSet = MMap[(NodeT, BitSet, NodeT), PathT]()
    var nDone = 0
    var nClashes = 0
    var nDups = 0

    // Paths already generated, in order of length - we typically only generate paths(0) since that is the TSP solution
    val paths = Buffer[PathData]()

    override def dumpStats(indent: Int): Unit = {
      (0 to indent).foreach { i => print("  ") }
      println(f"                                                                                   pg3 $M:${if(from0)"0"else"x"}-${if(to0)"0"else"x"} #paths ${paths.size} #lefts $iLeftNext #rights $iRightNext #done ${nDone} #dups ${nDups} #pending ${pendingPaths.size} #clashes ${nClashes}")
      // paths.foreach { pd =>
      //   (0 to indent).foreach { i => print("  ") }
      //   println(f"                                                                                         ${pd.length}%.4f ${pd.path}")
      // }
      leftPathGen.dumpStats(indent+1)
      rightPathGen.dumpStats(indent+1)
    }

    override def getPath(i: Int): Option[PathData] = {
      fillTo(i)
      //println(f"                                                                                   pg2 0to0 i = $i: #lefts $iLeftNext #rights $iRightNext #pending ${pendingPaths.size}")
      if(i < paths.size) Some(paths(i)) else None
    }

    def inverseNodeSet(nodeSet: BitSet, edgeNode: NodeT): BitSet = {
      allNon0NodesBitset -- nodeSet - edgeNode
    }

    /**
      * Generate paths up to the i'th path.
      */
    def fillTo(i: Int): Unit = {
      while(paths.size <= i && (pendingPaths.nonEmpty || !leftDone || !rightDone)) {
        doNext()
      }
    }

    def bumpLeft(): Unit = {
      iLeftNext = iLeftNext + 1
      leftPathGen.getPath(iLeftNext) match {
        case None =>
          leftDone = true
          // println(s"                                         left done after $iLeftNext subpaths")
        case Some(pathData) =>
          leftNext = pathData
          // println(f"                                         left $iLeftNext = ${pathData.path.toList} len ${pathData.length}%.4f")
      }
    }

    def bumpRight(): Unit = {
      iRightNext = iRightNext + 1
      rightPathGen.getPath(iRightNext) match {
        case None =>
          rightDone = true
          // println(f"                                                                                                         right done after $iRightNext subpaths")
        case Some(pathData) =>
          rightNext = pathData
          // println(f"                                                                                                         right $iRightNext = ${pathData.path.toList} len ${pathData.length}%.4f")
      }
    }

    def addLeft(iLeft: Int, left: PathData): Unit = {
      // Add to the left cache
      leftPathsByLast(left.last) += iLeft

      // Add first right match
      val rightMatches = rightPathsByFirst(left.last)
      if(rightMatches.nonEmpty) {
        addPendingPath(iLeft, iRight = rightMatches(0), linkNode = left.last, iLeftMatch = -1, iRightMatch = 0, iMatchLimit = rightMatches.size)
      }
    }

    def addRight(iRight: Int, right: PathData): Unit = {
      rightPathsByFirst(right.head) += iRight

      // Add first left match
      val leftMatches = leftPathsByLast(right.head)
      if(leftMatches.nonEmpty) {
        addPendingPath(iLeft = leftMatches(0), iRight, linkNode = right.head, iLeftMatch = 0, iRightMatch = -1, iMatchLimit = leftMatches.size)
      }
    }

    def addPendingPath(iLeft: Int, iRight: Int, linkNode: NodeT, iLeftMatch: Int, iRightMatch: Int, iMatchLimit: Int): Unit = {
      val left = leftPathGen.getPath(iLeft).get
      val right = rightPathGen.getPath(iRight).get
      val pendingPath = (left.length + right.length, iLeft, iRight, linkNode, iLeftMatch, iRightMatch, iMatchLimit)
      // if(paths.isEmpty && pendingPaths.isEmpty) {
      //   println(f"                                                                                                    first pending path left #${iLeft} right #${iRight} #lefts ${iLeftNext} #rights ${iRightNext} - len ${pendingPath._1}%.4f ${left.path.toList} + ${right.path.toList}")
      // }
      pendingPaths += pendingPath
      // println(f"                                         added pending path len ${pendingPath._1}%.4f ${left.path.toList} + ${right.path.toList}")
      updateMinPendingLengths()
    }

    def updateMinPendingLengths(): Unit = {
      val (minLength, minILeft, minIRight, _, _, _, _) = pendingPaths.head
      val minLeft = leftPathGen.getPath(minILeft).get
      val minRight = rightPathGen.getPath(minIRight).get
      minPendingLeftLength = minLeft.length
      minPendingRightLength = minRight.length
      // println(f"                                         min(pending) is now len $minLength%.4f ${minLeft.path.toList} + ${minRight.path.toList}")
    }

    def doNextPending(): Unit = {
      nDone = nDone + 1
      val nextPath = pendingPaths.head
      pendingPaths -= nextPath
      val (length, iLeft, iRight, linkNode, iLeftMatch, iRightMatch, iMatchLimit) = nextPath
      val left = leftPathGen.getPath(iLeft).get
      val right = rightPathGen.getPath(iRight).get
      //println(f"                                                                              releasing $iLeft len ${left.length}%.4f + $iRight len ${right.length}%.4f min ($minLeftLength%.4f $minRightLength%.4f) next $iLeftNext len ${leftNext.length}%.4f $iRightNext len ${rightNext.length}%.4f")
      addPath(left, right)
      // println(f"                                         removed pending path len ${nextPath._1}%.4f ${left.path.toList} + ${right.path.toList}")

      // Add the next match, if there is one
      if(iLeftMatch != -1) {
        val iMatchNext = iLeftMatch + 1
        if(iMatchNext < iMatchLimit) {
          val leftMatches = leftPathsByLast(linkNode)
          val iLeftNext = leftMatches(iMatchNext)
          addPendingPath(iLeftNext, iRight, linkNode, iMatchNext, iRightMatch, iMatchLimit)
        }
      }

      if(iRightMatch != -1) {
        val iMatchNext = iRightMatch + 1
        if(iMatchNext < iMatchLimit) {
          val rightMatches = rightPathsByFirst(linkNode)
          val iRightNext = rightMatches(iMatchNext)
          addPendingPath(iLeft, iRightNext, linkNode, iLeftMatch, iMatchNext, iMatchLimit)
        }
      }

      if(pendingPaths.isEmpty) {
        // println(f"                                         pending is now empty")
      }
      else {
        updateMinPendingLengths()
      }
    }

    def addPath(left: PathData, right: PathData): Unit = {
      // We can patch them together as long as we don't visit any node twice
      if(left.leftInners.intersect(right.rightInners).isEmpty) {
        // Success - patch the left and right paths together
        val path = left.path ++ right.path.tail
        val inners = BitSet(path.tail.init: _*)
        val key = (path.head, inners, path.last)
        //println(f"                       released path len ${left.length + right.length}%.4f - ${path.toList} = ${left.path.toList} + ${right.path.toList} ... l.leftInners ${left.leftInners} r.rightInners ${right.rightInners}")
        // println(f"                       after #lefts $iLeftNext and #rights $iRightNext - still ${pendingPaths.size} pending")
        pathsByInteriorSet.get(key) match {
          case None =>
            // No better path through the same nodes - this is a genuine new path
            pathsByInteriorSet(key) = path
            paths += mkPathData(path, from0, to0)
          case Some(betterPath) =>
            // Ignore this path - we already have a better one through the same nodes
            nDups = nDups + 1
            // println(f"                       ignored - we already have len ${length(betterPath)}%.4f ${betterPath.toList}")
        }
      }
      else {
        nClashes = nClashes + 1
      }
    }

    def doNextLeft(): Unit = {
      val iLeft = iLeftNext
      val left = leftNext
      bumpLeft()
      addLeft(iLeft, left)
    }

    def doNextRight(): Unit = {
      val iRight = iRightNext
      val right = rightNext
      bumpRight()
      addRight(iRight, right)
    }

    def doNext(): Unit = {
      //// println(s"look at new pair $iLeftNext and $iRightNext")
      if(iLeftNext == 0 && iRightNext == 0) {
        // Seed with the first left and right
        doNextLeft()
        doNextRight()
      }
      else {
        // First priority is releasing a pending path
        val minPendingLength = minPendingLeftLength + minPendingRightLength
        if(pendingPaths.nonEmpty
          /*&& (leftDone || minPendingLeftLength - minLeftLength <= leftNext.length - minPendingLeftLength)
           && (rightDone || minPendingRightLength - minRightLength <= rightNext.length - minPendingRightLength)*/
           && (leftDone || minPendingLength <= leftNext.length + minRightLength)
           && (rightDone || minPendingLength <= minLeftLength + rightNext.length)
        ) {

          // println("          doing next pending")
          doNextPending()
        }
        else {
          // Move either the left or right forward by 1
          if(leftDone) {
            // println("          left done - doing right")
            doNextRight()
          }
          else if(rightDone) {
            // println("          right done - doing left")
            doNextLeft()
          }
          else {
            // println(f"         left $iLeftNext len ${leftNext.length}%.4f + min(right) $minRightLength%.4f < min(left) $minLeftLength%.4f + right $iRightNext ${rightNext.length}%.4f")
            if(leftNext.length + minRightLength < minLeftLength + rightNext.length) {
              doNextLeft()
            }
            else {
              doNextRight()
            }
          }
        }
      }
    }

  }

  case class PathData2(head: NodeT, head2: NodeT, leftInners: BitSet, rightInners: BitSet, last: NodeT, last2: NodeT, path: PathT, length: DistanceT)

  def mkPathData2(path: PathT, from0: Boolean, to0: Boolean): PathData2 = {
    val init = path.init
    val leftInners = if(from0) init.tail else init
    val tail = path.tail
    val rightInners = if(to0) tail.init else tail
    PathData2(path.head, tail.head, leftInners = BitSet(leftInners: _*), rightInners = BitSet(rightInners: _*), init.last, path.last, path.toArray, length(path))
  }

  /**
    * Generate paths by patching together two paths of approximately half the length.
    * For the special case of the top-level PathGen, we can immediately match
    *   left & right paths by their last and head node, respectively, and the inverse
    *   of their internal nodes.
    * Use two nodes for the patch point.
    */
  class RecursivePathGen3x2(M: Int, from0: Boolean, to0: Boolean, factory: PathGenFactory)
      extends PathGen(M, from0, to0) {

    val leftPathGen = factory.getPathGen((M+3)/2, from0, to0 = false)

    val rightPathGen = factory.getPathGen((M+2)/2, from0 = false, to0)

    // leftPathsByLast(last-node) = indexes of left paths ending in last-node
    val leftPathsByLast = Array.fill(N,N) { Buffer[Int]() }

    // rightPathsByFirst(first-node) = indexes of right paths beginning with last-node
    val rightPathsByFirst = Array.fill(N,N) { Buffer[Int]() }

    // Seed the left paths
    var leftDone = false
    var iLeftNext = 0
    var leftNext: PathData2 = mkPathData2(leftPathGen.getPath(0).get.path, from0, to0)
    val minLeftLength = leftNext.length

    // Seed the right paths
    var rightDone = false
    var iRightNext = 0
    var rightNext: PathData2 = mkPathData2(rightPathGen.getPath(0).get.path, from0, to0)
    val minRightLength = rightNext.length

    val allNon0NodesBitset = BitSet((1 to N-1): _*)

    // Paths pending release, ordered by path length.
    // A path is released (published) once we have looked far enough forward in both left and right
    //   subpaths to prove that there can be no shorter path.
    // Set(length, left-index, right-index, linkNode1, linkNode2, left-max, right-max)
    val pendingPaths = MSortedSet[(DistanceT, Int, Int, NodeT, NodeT, Int, Int, Int)]()
    var minPendingLeftLength = 0.0
    var minPendingRightLength = 0.0

    // Paths already generated, indexed on the triple of (head, set of internal nodes, last).
    // Used to eliminate obviously inferior paths comprising the same two end-points,
    //   and the same interior nodes in a different (and longer path) order.
    val pathsByInteriorSet = MMap[(NodeT, BitSet, NodeT), PathT]()
    var nDone = 0
    var nClashes = 0
    var nDups = 0

    // Paths already generated, in order of length - we typically only generate paths(0) since that is the TSP solution
    val paths = Buffer[PathData2]()

    override def dumpStats(indent: Int): Unit = {
      (0 to indent).foreach { i => print("  ") }
      println(f"                                                                                   pg3x2 $M:${if(from0)"0"else"x"}-${if(to0)"0"else"x"} #paths ${paths.size} #lefts $iLeftNext #rights $iRightNext #done ${nDone} #dups ${nDups} #pending ${pendingPaths.size} #clashes ${nClashes}")
      // paths.foreach { pd =>
      //   (0 to indent).foreach { i => print("  ") }
      //   println(f"                                                                                         ${pd.length}%.4f ${pd.path}")
      // }
      leftPathGen.dumpStats(indent+1)
      rightPathGen.dumpStats(indent+1)
    }

    override def getPath(i: Int): Option[PathData] = {
      fillTo(i)
      //println(f"                                                                                   pg2 0to0 i = $i: #lefts $iLeftNext #rights $iRightNext #pending ${pendingPaths.size}")
      if(i < paths.size) Some(mkPathData(paths(i).path, from0, to0)) else None
    }

    def inverseNodeSet(nodeSet: BitSet, edgeNode: NodeT): BitSet = {
      allNon0NodesBitset -- nodeSet - edgeNode
    }

    /**
      * Generate paths up to the i'th path.
      */
    def fillTo(i: Int): Unit = {
      while(paths.size <= i && (pendingPaths.nonEmpty || !leftDone || !rightDone)) {
        doNext()
      }
    }

    def bumpLeft(): Unit = {
      iLeftNext = iLeftNext + 1
      leftPathGen.getPath(iLeftNext) match {
        case None =>
          leftDone = true
          // println(s"                                         left done after $iLeftNext subpaths")
        case Some(pathData) =>
          leftNext = mkPathData2(pathData.path, from0, to0)
          // println(f"                                         left $iLeftNext = ${pathData.path.toList} len ${pathData.length}%.4f")
      }
    }

    def bumpRight(): Unit = {
      iRightNext = iRightNext + 1
      rightPathGen.getPath(iRightNext) match {
        case None =>
          rightDone = true
          // println(f"                                                                                                         right done after $iRightNext subpaths")
        case Some(pathData) =>
          rightNext = mkPathData2(pathData.path, from0, to0)
          // println(f"                                                                                                         right $iRightNext = ${pathData.path.toList} len ${pathData.length}%.4f")
      }
    }

    def addLeft(iLeft: Int, left: PathData2): Unit = {
      // Add to the left cache
      leftPathsByLast(left.last)(left.last2) += iLeft

      // Add first right match
      val rightMatches = rightPathsByFirst(left.last)(left.last2)
      if(rightMatches.nonEmpty) {
        addPendingPath(iLeft, iRight = rightMatches(0), linkNode = left.last, linkNode2 = left.last2, iLeftMatch = -1, iRightMatch = 0, iMatchLimit = rightMatches.size)
      }
    }

    def addRight(iRight: Int, right: PathData2): Unit = {
      rightPathsByFirst(right.head)(right.head2) += iRight

      // Add first left match
      val leftMatches = leftPathsByLast(right.head)(right.head2)
      if(leftMatches.nonEmpty) {
        addPendingPath(iLeft = leftMatches(0), iRight, linkNode = right.head, linkNode2 = right.head2, iLeftMatch = 0, iRightMatch = -1, iMatchLimit = leftMatches.size)
      }
    }

    def addPendingPath(iLeft: Int, iRight: Int, linkNode: NodeT, linkNode2: NodeT, iLeftMatch: Int, iRightMatch: Int, iMatchLimit: Int): Unit = {
      val left = leftPathGen.getPath(iLeft).get
      val right = rightPathGen.getPath(iRight).get
      val pendingPath = (left.length + right.length, iLeft, iRight, linkNode, linkNode2, iLeftMatch, iRightMatch, iMatchLimit)
      // if(paths.isEmpty && pendingPaths.isEmpty) {
      //   println(f"                                                                                                    first pending path left #${iLeft} right #${iRight} #lefts ${iLeftNext} #rights ${iRightNext} - len ${pendingPath._1}%.4f ${left.path.toList} + ${right.path.toList}")
      // }
      pendingPaths += pendingPath
      // println(f"                                         added pending path len ${pendingPath._1}%.4f ${left.path.toList} + ${right.path.toList}")
      updateMinPendingLengths()
    }

    def updateMinPendingLengths(): Unit = {
      val (minLength, minILeft, minIRight, _, _, _, _, _) = pendingPaths.head
      val minLeft = leftPathGen.getPath(minILeft).get
      val minRight = rightPathGen.getPath(minIRight).get
      minPendingLeftLength = minLeft.length
      minPendingRightLength = minRight.length
      // println(f"                                         min(pending) is now len $minLength%.4f ${minLeft.path.toList} + ${minRight.path.toList}")
    }

    def doNextPending(): Unit = {
      nDone = nDone + 1
      val nextPath = pendingPaths.head
      pendingPaths -= nextPath
      val (length, iLeft, iRight, linkNode, linkNode2, iLeftMatch, iRightMatch, iMatchLimit) = nextPath
      val left = mkPathData2(leftPathGen.getPath(iLeft).get.path, from0, to0)
      val right = mkPathData2(rightPathGen.getPath(iRight).get.path, from0, to0)
      //println(f"                                                                              releasing $iLeft len ${left.length}%.4f + $iRight len ${right.length}%.4f min ($minLeftLength%.4f $minRightLength%.4f) next $iLeftNext len ${leftNext.length}%.4f $iRightNext len ${rightNext.length}%.4f")
      addPath(left, right)
      // println(f"                                         removed pending path len ${nextPath._1}%.4f ${left.path.toList} + ${right.path.toList}")

      // Add the next match, if there is one
      if(iLeftMatch != -1) {
        val iMatchNext = iLeftMatch + 1
        if(iMatchNext < iMatchLimit) {
          val leftMatches = leftPathsByLast(linkNode)(linkNode2)
          val iLeftNext = leftMatches(iMatchNext)
          addPendingPath(iLeftNext, iRight, linkNode, linkNode2, iMatchNext, iRightMatch, iMatchLimit)
        }
      }

      if(iRightMatch != -1) {
        val iMatchNext = iRightMatch + 1
        if(iMatchNext < iMatchLimit) {
          val rightMatches = rightPathsByFirst(linkNode)(linkNode2)
          val iRightNext = rightMatches(iMatchNext)
          addPendingPath(iLeft, iRightNext, linkNode, linkNode2, iLeftMatch, iMatchNext, iMatchLimit)
        }
      }

      if(pendingPaths.isEmpty) {
        // println(f"                                         pending is now empty")
      }
      else {
        updateMinPendingLengths()
      }
    }

    def addPath(left: PathData2, right: PathData2): Unit = {
      // We can patch them together as long as we don't visit any node twice
      if(left.leftInners.intersect(right.rightInners).isEmpty) {
        // Success - patch the left and right paths together
        val path = left.path ++ right.path.tail.tail
        val inners = BitSet(path.tail.init: _*)
        val key = (path.head, inners, path.last)
        //println(f"                       released path len ${left.length + right.length}%.4f - ${path.toList} = ${left.path.toList} + ${right.path.toList} ... l.leftInners ${left.leftInners} r.rightInners ${right.rightInners}")
        // println(f"                       after #lefts $iLeftNext and #rights $iRightNext - still ${pendingPaths.size} pending")
        pathsByInteriorSet.get(key) match {
          case None =>
            // No better path through the same nodes - this is a genuine new path
            pathsByInteriorSet(key) = path
            paths += mkPathData2(path, from0, to0)
          case Some(betterPath) =>
            // Ignore this path - we already have a better one through the same nodes
            nDups = nDups + 1
            // println(f"                       ignored - we already have len ${length(betterPath)}%.4f ${betterPath.toList}")
        }
      }
      else {
        nClashes = nClashes + 1
      }
    }

    def doNextLeft(): Unit = {
      val iLeft = iLeftNext
      val left = leftNext
      bumpLeft()
      addLeft(iLeft, left)
    }

    def doNextRight(): Unit = {
      val iRight = iRightNext
      val right = rightNext
      bumpRight()
      addRight(iRight, right)
    }

    def doNext(): Unit = {
      //// println(s"look at new pair $iLeftNext and $iRightNext")
      if(iLeftNext == 0 && iRightNext == 0) {
        // Seed with the first left and right
        doNextLeft()
        doNextRight()
      }
      else {
        // First priority is releasing a pending path
        val minPendingLength = minPendingLeftLength + minPendingRightLength
        if(pendingPaths.nonEmpty
          /*&& (leftDone || minPendingLeftLength - minLeftLength <= leftNext.length - minPendingLeftLength)
           && (rightDone || minPendingRightLength - minRightLength <= rightNext.length - minPendingRightLength)*/
           && (leftDone || minPendingLength <= leftNext.length + minRightLength)
           && (rightDone || minPendingLength <= minLeftLength + rightNext.length)
        ) {

          // println("          doing next pending")
          doNextPending()
        }
        else {
          // Move either the left or right forward by 1
          if(leftDone) {
            // println("          left done - doing right")
            doNextRight()
          }
          else if(rightDone) {
            // println("          right done - doing left")
            doNextLeft()
          }
          else {
            // println(f"         left $iLeftNext len ${leftNext.length}%.4f + min(right) $minRightLength%.4f < min(left) $minLeftLength%.4f + right $iRightNext ${rightNext.length}%.4f")
            if(leftNext.length + minRightLength < minLeftLength + rightNext.length) {
              doNextLeft()
            }
            else {
              doNextRight()
            }
          }
        }
      }
    }

  }
  
  /**
    * Generate paths by patching together two paths of approximately half the length.
    */
  class RecursivePathGen(M: Int, from0: Boolean, to0: Boolean, factory: PathGenFactory)
      extends PathGen(M, from0, to0) {
    val leftPaths = factory.getPathGen((M+2)/2, from0, to0 = false)
    var iLeftMax = 0

    val rightPaths = factory.getPathGen((M+1)/2, from0 = false, to0)
    var iRightMax = 0

    // Paths already generated, in order of length
    val paths = Buffer[PathData]()

    // Paths already generated, indexed on the triple of (head, set of internal nodes, last).
    // Used to eliminate obviously inferior paths comprising the same two end-points,
    //   and the same interior nodes in a different (and longer path) order.
    val pathsByInteriorSet = MMap[(NodeT, BitSet, NodeT), PathT]()
    var nDups = 0

    // (left, right) pairs ordered by total length.
    val todo = MSortedSet[(Double, Int, Int)]()
    // Seed the todo list
    addTodo(iLeft = 0, iRight = 0)

    var nDone = 0

    override def dumpStats(indent: Int): Unit = {
      (0 to indent).foreach { i => print("  ") }
      println(f"                                                                                   pg $M:${if(from0)"0"else"x"}-${if(to0)"0"else"x"} #paths ${paths.size} #lefts $iLeftMax #rights $iRightMax #done ${nDone} #dups ${nDups} #todo ${todo.size}")
      // paths.foreach { pd =>
      //   (0 to indent).foreach { i => print("  ") }
      //   println(f"                                                                                         ${pd.length}%.4f ${pd.path}")
      // }
      leftPaths.dumpStats(indent+1)
      rightPaths.dumpStats(indent+1)
    }

    // Add a left/right pair to the todo set
    def addTodo(iLeft: Int, iRight: Int): Unit = {
      val maybeLeft = leftPaths.getPath(iLeft)
      val maybeRight = rightPaths.getPath(iRight)
      (maybeLeft, maybeRight) match {
        case (Some(left), Some(right)) =>
          val item = (left.length + right.length, iLeft, iRight)
          todo += item
        case (_, _) => /*ignore - no more child paths*/
      }
    }


    override def getPath(i: Int): Option[PathData] = {
      fillTo(i)
      // if(from0 && to0) {
      //   val currLeft = leftPaths.getPath(iLeftMax).get
      //   val currRight = rightPaths.getPath(iRightMax).get
      //   println(f"                                                                                   pg 0to0 i = $i: #lefts $iLeftMax #rights $iRightMax #done $nDone #todo ${todo.size} curr left len ${currLeft.length}%.4f right leng ${currRight.length}%.4f")
      // }
      if(i < paths.size) Some(paths(i)) else None
    }

    /**
      * Generate paths up to the i'th path.
      */
    def fillTo(i: Int): Unit = {
      while(paths.size <= i && todo.nonEmpty) {
        nextPair()
      }
    }

    def nextPair(): Unit = {
      nDone = nDone + 1

      // Remove the next shortest left/right pair from the todo set - it might not actually be a matching pair
      val next = todo.head
      todo -= next

      val (len, iLeft, iRight) = next

      val left = leftPaths.getPath(iLeft).get
      val right = rightPaths.getPath(iRight).get

      if(iLeftMax < iLeft) iLeftMax = iLeft
      if(iRightMax < iRight) iRightMax = iRight

      // it's a match if the end point is the same and none of the middle points intersect
      if(left.last == right.head) {
        // Ok, we can patch them together as long as we don't visit any node twice
        if(left.leftInners.intersect(right.rightInners).isEmpty) {
          // Success - patch the left and right paths together
          val path = left.path ++ right.path.tail
          val inners = BitSet(path.tail.init: _*)
          val key = (path.head, inners, path.last)
          pathsByInteriorSet.get(key) match {
            case None =>
              // No better path through the same nodes - this is a genuine new path
              pathsByInteriorSet(key) = path
              paths += mkPathData(path, from0, to0)
            case Some(betterPath) =>
              // Ignore this path - we already have a better one through the same nodes
              nDups = nDups + 1
          }
        }
      }
      // Now add the next pairs to the todo list (they might already be there)
      addTodo(iLeft, iRight+1)
      addTodo(iLeft+1, iRight)
    }
  }

  /**
    * TSP by recursive minimum path generation and patching.
    */
  def pgMinHamCycle: PathT = {
    val pgFactory = new PgFactory
    val pathGen = pgFactory.getPathGen(M = N+1, from0 = true, to0 = true)
    val result = pathGen.getPath(0).get
    pathGen.dumpStats(0)
    result.path.toList /*cos other ones end up with a list*/
  }

  def pg2MinHamCycle: PathT = {
    val pg2Factory = new Pg2Factory
    val pathGen = pg2Factory.getPathGen(M = N+1, from0 = true, to0 = true)
    val result = pathGen.getPath(0).get
    pathGen.dumpStats(0)
    result.path.toList /*cos other ones end up with a list*/
  }

  def pg3MinHamCycle: PathT = {
    val pg3Factory = new Pg3Factory
    val pathGen = pg3Factory.getPathGen(M = N+1, from0 = true, to0 = true)
    val result = pathGen.getPath(0).get
    pathGen.dumpStats(0)
    result.path.toList /*cos other ones end up with a list*/
  }

  def pg3x2MinHamCycle: PathT = {
    val pg3x2Factory = new Pg3x2Factory
    val pathGen = pg3x2Factory.getPathGen(M = N+1, from0 = true, to0 = true)
    val result = pathGen.getPath(0).get
    pathGen.dumpStats(0)
    result.path.toList /*cos other ones end up with a list*/
  }
}

object Tsp {

  def time[A](work: => A): A = {
    System.gc()
    Thread.sleep(1)
    val startMs = System.currentTimeMillis
    try {
      work
    }
    finally {
      val endMs = System.currentTimeMillis
      println(s"[${endMs-startMs}ms]")
      System.gc()
      Thread.sleep(1)
    }
  }

  def main(args: Array[String]): Unit = {
    println("Hello, world!")
  }

  val MaxNForAvg = 10
  val MaxNForBrute = 10
  val MaxNForDp = 10
  val MaxNForFold = 10
  val MaxNForPg = 0
  val MaxNForPgN = 40
  val MaxNForPg2 = 0
  val MaxNForPg2N = 40
  val MaxNForPg3 = 0
  val MaxNForPg3N = 40
  val MaxNForPg3x2N = 40
  val MaxNForGreedy = 1000

  def c(n1: NodeT, n2: NodeT) = 1.0

  //(0 to 5).zip(0 to 5).collect { case (i, j) if i != j => Seq(i, j) }.foreach(println)
  //(0 to 5).combinations(2).map(_.permutations).flatten.toSeq.sorted.foreach(println)
  //(0 to 5).map { i => (0 to 5).collect { case j if i != j => Seq(i, j) } }.flatten.foreach(println)

  // println("Constant d(i,j) = 1.0")
  // hamCycles(N).foreach { p =>
  //   val len = Path(p).length(c)
  //   println(s"$p => length $len")
  // }
  // val cAvg = avgHamCycle(TspConfig(N, c))
  // val cMin = minHamCycle(TspConfig(N, c))
  // val cMinLen = Path(cMin).length(c)
  // println(s"   min $cMin -> $cMinLen, avg $cAvg")

  // println()

  // println("Random d(i,j)")
  println("Random 2D d(i,j)")

  for(N <- 2 to 40) {
    println(s"----------------- N = $N --------------------")
    for (i <- 1 to 2) {
      println()

      //val tsp = Tsp(N, MetricUtils.random(N))
      val tsp = Tsp(N, MetricUtils.random2d(N))
      val tspNorm = tsp.normalised
      // val tspDen = tsp.denormalised

      if(N <= MaxNForAvg) time {
        val dAvg = tsp.avgHamCycle
        println(f"   avg      $dAvg%.6f")
      }
      if(N <= MaxNForBrute) time {
        val dMin = tsp.bruteMinHamCycle
        val dMinLen = tsp.length(dMin)
        println(f"   brute    $dMin -> $dMinLen%.6f")
      }
      // if(N <= MaxNForBrute) time {
      //   val dMinNorm = tspNorm.bruteMinHamCycle
      //   val dMinNormLen = tsp.length(dMinNorm)
      //   println(f"N: brute    $dMinNorm -> $dMinNormLen%.6f")
      // }
      // if(N <= MaxNForBrute) time {
      //   val dMinDen = tspDen.bruteMinHamCycle
      //   val dMinDenLen = tsp.length(dMinDen)
      //   println(f"D: brute    $dMinDen -> $dMinDenLen%.6f")
      // }
      if(N <= MaxNForDp) time {
        val dDpMin = tsp.dpMinHamCycle
        val dDpMinLen = tsp.length(dDpMin)
        println(f"   dp       $dDpMin -> $dDpMinLen%.6f")
      }
      if(N <= MaxNForFold) time {
        val dFoldDpMin = tsp.foldDpMinHamCycle
        val dFoldDpMinLen = tsp.length(dFoldDpMin)
        println(f"   fold     $dFoldDpMin -> $dFoldDpMinLen%.6f")
      }
      if(N <= MaxNForPg) time {
        //println(f"   path-gen...")
        val dPgMin = tsp.pgMinHamCycle
        val dPgMinLen = tsp.length(dPgMin)
        println(f"   path-gen $dPgMin -> $dPgMinLen%.6f")
      }
      if(N <= MaxNForPgN) time {
        val dPgNormMin = tspNorm.pgMinHamCycle
        val dPgNormMinLen = tsp.length(dPgNormMin)
        println(f"N: path-gen $dPgNormMin -> $dPgNormMinLen%.6f")
      }
      if(N <= MaxNForPg2) time {
        //println(f"   pg2...")
        val dPg2Min = tsp.pg2MinHamCycle
        val dPg2MinLen = tsp.length(dPg2Min)
        println(f"   pg2      $dPg2Min -> $dPg2MinLen%.6f")
      }
      if(N <= MaxNForPg2N) time {
        val dPg2NormMin = tspNorm.pg2MinHamCycle
        val dPg2NormMinLen = tsp.length(dPg2NormMin)
        println(f"N: pg2      $dPg2NormMin -> $dPg2NormMinLen%.6f")
      }
      if(N <= MaxNForPg3) time {
        //println(f"   pg3...")
        val dPg3Min = tsp.pg3MinHamCycle
        val dPg3MinLen = tsp.length(dPg3Min)
        println(f"   pg3      $dPg3Min -> $dPg3MinLen%.6f")
      }
      if(N <= MaxNForPg3N) time {
        val dPg3NormMin = tspNorm.pg3MinHamCycle
        val dPg3NormMinLen = tsp.length(dPg3NormMin)
        println(f"N: pg3      $dPg3NormMin -> $dPg3NormMinLen%.6f")
      }
      if(N <= MaxNForPg3x2N) time {
        val dPg3x2NormMin = tspNorm.pg3x2MinHamCycle
        val dPg3x2NormMinLen = tsp.length(dPg3x2NormMin)
        println(f"N: pg3x2    $dPg3x2NormMin -> $dPg3x2NormMinLen%.6f")
      }
      // if(N <= MaxNForPg) time {
      //   val dPgDenMin = tspDen.pgMinHamCycle
      //   val dPgDenMinLen = tsp.length(dPgDenMin)
      //   println(f"D: path-gen $dPgDenMin -> $dPgDenMinLen%.6f")
      // }
      if(N <= MaxNForGreedy) time {
        val dGreedy = tsp.greedyHamCycle()
        val dGreedyLen = tsp.length(dGreedy)
        println(f"   greedy   $dGreedy -> $dGreedyLen%.6f")
      }
      if(N <= MaxNForGreedy) time {
        val dBestGreedy = tsp.bestGreedyHamCycle
        val dBestGreedyLen = tsp.length(dBestGreedy)
        println(f"   greedyN  $dBestGreedy -> $dBestGreedyLen%.6f")
      }
    }
    println()
  }

  // for(NN <- 3 to 0) {
  //   val tspNN = Tsp(NN, MetricUtils.random(NN))

  //   val M = NN+1

  //   val pg2Mtt = tspNN.getPathGen2(M, true, true)
  //   pg2Mtt.dump
  //   println
  //   println
  //   println
  //   println
  // }


  // val NN = 6
  // val tspNN = Tsp(NN, MetricUtils.random(NN))

  // val M = 4

  // val pgMtt = tspNN.getPathGen(M, true, true)
  // pgMtt.dump

  // val pgMtf = tspNN.getPathGen(M, true, false)
  // pgMtf.dump

  // val pgMft = tspNN.getPathGen(M, false, true)
  // pgMft.dump

  // val pgMff = tspNN.getPathGen(M, false, false)
  // pgMff.dump
}

case class ArrayMetric(a: Array[Array[DistanceT]]) {
  // Metric function
  def d(n1: NodeT, n2: NodeT) = a(n1)(n2)
}

object MetricUtils {
  val r = new util.Random

  /**
    *  Generate a random distance function, with edges in [0.0, 1.0)
    */
  def random(N: Int): (NodeT, NodeT) => DistanceT = {
    // Generate a random NxN array
    val a = Array.fill(N, N) { r.nextDouble }
    // Zero out d(i,i)
    (0 to N-1).foreach { i => a(i)(i) = 0.0 }
    ArrayMetric(a).d
  }

  /**
    *  Generate a distance function from a random set of points in the unit square.
    */
  def random2d(N: Int): (NodeT, NodeT) => DistanceT = {
    // Generate a random Nx2 array of points
    val p = Array.fill(N, 2) { r.nextDouble }

    // d(i,j) is the 2d metric function between p(i) and p(j)
    def d(i: Int, j: Int): Double = {
      Math.sqrt( Math.pow(p(i)(0) - p(j)(0), 2) + Math.pow(p(i)(1) - p(j)(1), 2) )
    }

    // Generate a 0 NxN array
    val a = Array.fill(N, N) { 0.0 }
    (0 to N-1).foreach { i => (0 to N-1).foreach { j => a(i)(j) = d(i,j) } }

    // Return the metric
    ArrayMetric(a).d
  }

  /**
    * Normalise the distance function, as follows:
    * For each node i, replace d(i,j) with d(i,j) - min(m, d(i,m))
    * For each node i, replace d(j,i) with d(j,i) - min(m, d(m,i))
    * The aim is produce a more 'balanced' distance metric with the same TSP solution path.
    */
  def normalise(N: Int, d: (NodeT, NodeT) => DistanceT): (NodeT, NodeT) => DistanceT = {
    // Generate a 0 NxN array
    val a = Array.fill(N, N) { 0.0 }

    // Initialise the array to exit-normalised distances
    (0 to N-1).foreach { i =>
      val minDij = (0 to N-1).map { j =>
        if(i == j) 1000000000.0 else d(i,j)
      }.min
      (0 to N-1).foreach { j =>
        a(i)(j) = if(i == j) 0.0 else d(i,j) - minDij
        //println(f"      a($i,$j) = ${a(i)(j)}%.4f = ${d(i,j)}%.4f - ${minDij}%.4f")
      }
    }

    // Perform entrance-normalisation on the array
    (0 to N-1).foreach { i =>
      val minAji = (0 to N-1).map { j =>
        if(i == j) 1000000000.0 else a(j)(i)
      }.min
      (0 to N-1).foreach { j =>
        a(j)(i) = if(i == j) 0.0 else a(j)(i) - minAji
        //println(f"      a($j,$i) = ${a(j)(i)}%.4f -= ${minAji}%.4f")
      }
    }

    // Return the metric
    ArrayMetric(a).d
  }

  /**
    * Denormalise the distance function, as follows:
    * For each node i, replace d(i,j) with d(i,j) + j
    * For each node i, replace d(j,i) with d(j,i) + N*j
    * The aim is produce a less 'balanced' distance metric with the same TSP solution path.
    */
  def denormalise(N: Int, d: (NodeT, NodeT) => DistanceT): (NodeT, NodeT) => DistanceT = {
    // Generate a 0 NxN array
    val a = Array.fill(N, N) { 0.0 }

    // Initialise the array to exit-normalised distances
    (0 to N-1).foreach { i =>
      (0 to N-1).foreach { j =>
        a(i)(j) = if(i == j) 0.0 else d(i,j) + j
      }
    }

    // Perform entrance-normalisation on the array
    (0 to N-1).foreach { i =>
      (0 to N-1).foreach { j =>
        a(j)(i) = if(i == j) 0.0 else a(j)(i) + j*N
      }
    }

    // Return the metric
    ArrayMetric(a).d
  }
}

