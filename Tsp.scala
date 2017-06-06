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
case class Tsp(N: NodeT, d: (NodeT, NodeT) => DistanceT) {


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

  val PathGenCache = MMap[(Int, Boolean, Boolean), PathGen]()

  def getPathGen(M: Int, from0: Boolean = false, to0: Boolean = false): PathGen = {
    PathGenCache.synchronized {
      PathGenCache.getOrElseUpdate((M, from0, to0), buildPathGen(M, from0, to0))
    }
  }

  def buildPathGen(M: Int, from0: Boolean, to0: Boolean): PathGen = {
//println(s"buildPathGen($M, $from0, $to0)")
    (M, from0, to0) match {
      case (2, false, false) => new EdgesNon0
      case (2, false, true) => new EdgesTo0
      case (2, true, false) => new EdgesFrom0
      case (2, true, true) => new Edge0To0

      case (_, _, _) => new RecursivePathGen(M, from0, to0)
    }
  }

  case class PathData(head: NodeT, /*matchNodes: Set[NodeT],*/ last: NodeT, path: PathT)

  def mkPathData(path: PathT) = PathData(path.head, path.last, path.toArray/*force to array*/)

  /**
    * M is the number of nodes in a path, i.e. M-1 edges.
    */
  abstract class PathGen(M: Int, from0: Boolean, to0: Boolean) {

    /**
      * @return the i'th shortest path of length M (or None if there are fewer than i paths)
      */
    def getPath(i: Int): Option[PathData]

    var dumped = false

    def dump: Unit = {}

    def dumpRec: Unit = {}
  }

  class PathGenFromArray(M: Int, from0: Boolean, to0: Boolean, paths: Array[PathData])
      extends PathGen(M, from0, to0) {

    override def getPath(i: Int): Option[PathData] = if(i < paths.size) Some(paths(i)) else None
  }

  /**
    * Single-edge paths in increasing order of length.
    */
  class EdgesNon0 extends PathGenFromArray(M = 2, from0 = false, to0 = false, paths = edgesNon0.toArray.sortBy(length).map(mkPathData))

  /**
    * Single-edge edges from 0 in increasing order of length.
    */
  class EdgesFrom0 extends PathGenFromArray(M = 2, from0 = true, to0 = false, paths = (1 to N-1).map { i => Seq(0, i) }.toArray.sortBy(length).map(mkPathData))

  /**
    * Single-edge edges from 0 in increasing order of length.
    */
  class EdgesTo0 extends PathGenFromArray(M = 2, from0 = false, to0 = true, paths = (1 to N-1).map { i => Seq(i, 0) }.toArray.sortBy(length).map(mkPathData))

  /**
    * Pathological case edge 0 to 0
    */
  class Edge0To0 extends PathGenFromArray(M = 2, from0 = true, to0 = true, paths = Array(Seq(0, 0)).map(mkPathData))

  /**
    * Generate paths by patching together two paths of approximately half the length.
    */
  class RecursivePathGen(M: Int, from0: Boolean, to0: Boolean)
      extends PathGen(M, from0, to0) {
    val leftPaths = getPathGen((M+2)/2, from0, to0 = false)
    val leftLimit = 0

    val rightPaths = getPathGen((M+1)/2, from0 = false, to0)
    val rightLimit = 0

    // Paths already generated, in order of length
    val paths = Buffer[PathData]()

    // Paths already generated, indexed on the triple of (head, set of internal nodes, last).
    // Used to eliminate obviously inferior paths comprising the same two end-points,
    //   and the same interior nodes in a different (and longer path) order.
    val pathsByInteriorSet = MMap[(NodeT, Set[NodeT], NodeT), PathT]()

    // (left, right) pairs ordered by total length.
    val todo = MSortedSet[(Double, Int, Int)]()
    // Seed the todo list
    addTodo(iLeft = 0, iRight = 0)

    // For debug
    val pairsDone = Buffer[(Int, Int)]()
    val pathPairs = Buffer[(Int, Int)]()

    // Add a left/right pair to the todo set
    def addTodo(iLeft: Int, iRight: Int): Unit = {
      val maybeLeft = leftPaths.getPath(iLeft)
      val maybeRight = rightPaths.getPath(iRight)
      (maybeLeft, maybeRight) match {
        case (Some(left), Some(right)) =>
          val item = (length(left.path) + length(right.path), iLeft, iRight)
          todo += item
        case (_, _) => /*ignore - no more child paths*/
      }
      //println(s"                     todo -> ${todo}")
      //print("                         todo -> ")
      // todo.foreach { item =>
      //   val(len, i, j) = item
      //   val left = leftPaths.getPath(i).get
      //   val right = rightPaths.getPath(j).get
      //   print(f"[$len%.4f $i = $left len ${length(left)}%.4f ++ $j = $right len ${length(right)}%.4f] ")
      // }
      //println
    }


    override def getPath(i: Int): Option[PathData] = {
//println(s"RecursivePathGen($M, $from0, $to0).getPath($i) paths.size is ${paths.size}")
      fillTo(i)
      if(i < paths.size) Some(paths(i)) else None
    }

    /**
      * Generate paths up to the i'th path.
      */
    def fillTo(i: Int): Unit = {
      // if(M == N+1 && 0 < i) {
      //   new Exception(s"N = $N M = $M from0 = $from0 to0 = $to0 - seeking path $i").printStackTrace(System.out)
      // }
      if(paths.size <= i) {
        RecursivePathGen.this.synchronized {
          while(paths.size <= i && todo.nonEmpty) {
            // println(s"                                        N = $N M = $M from0 = $from0 to0 = $to0 - seeking path $i")
            nextPair()
          }
          // if(i < paths.size) {
          //   println(s"                                        N = $N M = $M from0 = $from0 to0 = $to0 - path $i ${pathPairs(i)} = ${paths(i)}")
          // }
          // else {
          //   println(s"                                        N = $N M = $M from0 = $from0 to0 = $to0 - no such path $i")
          // }
        }
      }
    }

    def internalNodeSet(path: PathT, ignoreHead: Boolean, ignoreLast: Boolean): Set[NodeT] = {
      // Optionally remove the head
      val headless = if(ignoreHead) path.tail else path
      // Optionally remove the last
      val internalNodes = if(ignoreLast) headless.init else headless
      // Transform to a set
      internalNodes.toSet
    }

    def nextPair(): Unit = {
//println(s"RecursivePathGen($M, $from0, $to0).nextPair - todo set has ${todo.size} pairs")
      // Remove the next shortest left/right pair from the todo set - it might not actually be a matching pair
      val next = todo.head
      todo -= next
      val (len, iLeft, iRight) = next
      //println(s"                                        N = $N M = $M from0 = $from0 to0 = $to0 -   looking at l/r pair ($iLeft, $iRight)")
      val itemDone = (iLeft, iRight)
      pairsDone += itemDone
      val left = leftPaths.getPath(iLeft).get
      val right = rightPaths.getPath(iRight).get
//println(s"RecursivePathGen($M, $from0, $to0).nextPair: length $len for ($iLeft, $iRight) = $left ++ ${right.reverse}")
      // it's a match if the end point is the same and none of the middle points intersect
      if(left.last == right.head) {
        // Ok, we can patch them together as long as we don't repeat any other node
        val leftInternalSet = internalNodeSet(left.path, ignoreHead = from0, ignoreLast = true)
        val rightInternalSet = internalNodeSet(right.path, ignoreHead = true, ignoreLast = to0)
        if(leftInternalSet.intersect(rightInternalSet).isEmpty) {
          // Success - patch the left and right paths together
          val path = left.path ++ right.path.tail
          val interiorNodeSet = path.tail.init.toSet
          val key = (path.head, interiorNodeSet, path.last)
          pathsByInteriorSet.get(key) match {
            case None =>
              // No better path through the same nodes - this is a genuine new path
              //println(s"                                    got him - length $len for path ${paths.length-1} = ${paths.last}")
              pathsByInteriorSet(key) = path
              paths += mkPathData(path)
              val pathPair = (iLeft, iRight)
              pathPairs += pathPair
            case Some(betterPath) =>
              // Ignore this path - we already have a better one through the same nodes
              //println(f"                              ignoring $path len ${length(path)}%.6f - $betterPath len ${length(betterPath)}%.6f is better")
              // if(path == betterPath) {
              //   println("                                                    !!!!!!!!!!! DUP")
              // }
          }
        }
      }
      // Now add the next pairs to the todo list (they might already be there)
      addTodo(iLeft, iRight+1)
      addTodo(iLeft+1, iRight)
    }

    override def dump: Unit = {
      println(s"                          N = $N M = $M from0 = $from0 to0 = $to0:")
      if(dumped) {
        println("                                      [already dumped]")
      }
      else {
        dumped = true

        var i = 0
        while(i < paths.length) {
          val path = paths(i)
          println(f"                                i = $i%3d len = ${length(path.path)}%.6f $path")
          i = i+1
        }
      }
    }

    override def dumpRec: Unit = {
      val alreadyDumped = dumped
      dump

      if(!alreadyDumped) {
        var i = 0
        pathPairs.foreach { case (iLeft, iRight) =>
          val left = leftPaths.getPath(iLeft).get
          val right = rightPaths.getPath(iRight).get
          println(f"                                path $i%3d: ($iLeft%3d, $iRight%3d) = $left + $right len ${length(left.path) + length(right.path)}%.6f")
          i = i+1
        }
        pairsDone.foreach { case (iLeft, iRight) =>
          val left = leftPaths.getPath(iLeft).get
          val right = rightPaths.getPath(iRight).get
          println(f"                                     done ($iLeft%3d, $iRight%3d) = $left + $right len ${length(left.path) + length(right.path)}%.6f")
        }
        todo.foreach { case (_, iLeft, iRight) =>
          val left = leftPaths.getPath(iLeft).get
          val right = rightPaths.getPath(iRight).get
          println(f"                                     todo ($iLeft%3d, $iRight%3d) = $left + $right len ${length(left.path) + length(right.path)}%.6f")
        }

        leftPaths.dumpRec
        rightPaths.dumpRec
      }
    }
  }

  /**
    * TSP by recursive minimum path generation and patching.
    */
  def pgMinHamCycle: PathT = {
    val pathGen = getPathGen(M = N+1, from0 = true, to0 = true)
    val result = pathGen.getPath(0).get
    //pathGen.dumpRec
    result.path.toList /*cos other ones end up with a list*/
  }

}

object Tsp {

  def time[A](work: => A): A = {
    val startMs = System.currentTimeMillis
    try {
      work
    }
    finally {
      val endMs = System.currentTimeMillis
      println(s"[${endMs-startMs}ms]")
    }
  }

  def main(args: Array[String]): Unit = {
    println("Hello, world!")
  }

  val MaxNForAvg = 10
  val MaxNForBrute = 10
  val MaxNForDp = 15
  val MaxNForFold = 13
  val MaxNForPg = 50
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

  println("Random d(i,j)")

  for(N <- 2 to 25/*25*/) {
    println(s"----------------- N = $N --------------------")
    for (i <- 1 to 2) {
      println()
      val tsp = Tsp(N, MetricUtils.random(N))
      if(N <= MaxNForAvg) time {
        val dAvg = tsp.avgHamCycle
        println(f"   avg      $dAvg%.6f")
      }
      if(N <= MaxNForBrute) time {
        val dMin = tsp.bruteMinHamCycle
        val dMinLen = tsp.length(dMin)
        println(f"   brute    $dMin -> $dMinLen%.6f")
      }
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
        val dPgMin = tsp.pgMinHamCycle
        val dPgMinLen = tsp.length(dPgMin)
        println(f"   path-gen $dPgMin -> $dPgMinLen%.6f")
      }
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
  def random(N: NodeT): (NodeT, NodeT) => DistanceT = {
    // Generate a random NxN array
    val a = Array.fill(N, N) { r.nextDouble }
    // Zero out d(i,i)
    (0 to N-1).foreach { i => a(i)(i) = 0.0 }
    ArrayMetric(a).d
  }
}

