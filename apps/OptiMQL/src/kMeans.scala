import optimql.compiler._
import optimql.library._
import optimql.shared._

import scala.virtualization.lms.common.Record
import scala.reflect.{RefinedManifest,SourceContext}

object kMeans extends OptiMQLApplicationCompiler with Types { this: OptiMQLApplicationCompiler =>
  type Data =  Record {
    val names: String
    val cluster: Int
    val murder: Double
    val assault: Int
    val pop: Int
    val rape: Double
  }

  type DataR =  Record {
    val murder: Double
    val assault: Int
    val pop: Int
    val rape: Double
  }

  def printUsage = {
    println("Usage: kmeans <input data file> [initmu data file]")
    exit(-1)
  }

  private val tol = 0.001 // tolerance (for convergence)
  private val k = 4 // num clusters

  private def findNearestCluster(x_i: Rep[DenseVector[Double]], mu: Rep[DenseMatrix[Double]]): Rep[Int] = {
    (mu mapRowsToVector { row => dist(x_i, row, SQUARE) }).minIndex
  }

  private def tableToMatrix[T:RefinedManifest](tab:Rep[Table[T]]): Rep[DenseMatrix[Double]] = {

    val a = tab.toArray
    val numCols = implicitly[RefinedManifest[T]].fields filter { case (_, man) => man != manifest[String] } length
    val elems = a flatMap { line =>
      array_fromseq(implicitly[RefinedManifest[T]].fields filter {
        case (_, man) => man != manifest[String] } map { case (name, _) => field[Double](line, name) } toSeq
      )
    }

    densematrix_fromarray(elems, tab.size, numCols)
  }

  def extractMF[T](x: Rep[Table[T]]): Manifest[T] = {
     //  println(x.tp.typeArguments)
     x.tp.typeArguments.head.asInstanceOf[Manifest[T]]
  }

  def main() = {
    if (args.length < 1) printUsage

    println(args.length)

    val sep = ","
    val data = Table.fromFile[Data](args(0), sep)
    val q = data Select(g => new Record {
      val murder = g.murder
      val assault = g.assault
      val pop = g.pop
      val rape = g.rape
    })

    implicit val man = extractMF(q).asInstanceOf[RefinedManifest[DataR]]
    val mat = tableToMatrix(q)
    val x = DenseTrainingSet(mat, DenseVector[Double]()) // no labels
    val m = x.numSamples
    val n = x.numFeatures
    val mu = (0::k, *) { i => x(randomInt(m)) }

    println("m:"+m+",n:"+n+",numClusters:"+k+",mu.numRows:"+mu.numRows)

    tic(mu)

    val newMu = untilconverged_withdiff(mu, tol){ (mu, iter) =>
      val c = (0::m) { e => findNearestCluster(x(e), mu) }

      val allWP = (0::m).groupByReduce(i => c(i), i => x(i).Clone, (a: Rep[DenseVector[Double]], b: Rep[DenseVector[Double]]) => a + b)
      val allP = (0::m).groupByReduce(i => c(i), i => 1, (a: Rep[Int], b: Rep[Int]) => a+b)

      (0::k,*) { j =>
        val weightedpoints = fhashmap_get(allWP, j)
        val points = fhashmap_get(allP, j)
        val d = if (points == 0) 1 else points
        weightedpoints / d
      }
    }((x, y) => dist(x, y, SQUARE)) // use SQUARE instead of the default EUC distance

    toc(newMu)
    newMu.pprint

    val test = data Select { line => new Record {
        val cluster = line.cluster
        val classification = findNearestCluster(DenseVector(line.murder, line.assault.toDouble, line.pop.toDouble, line.rape), newMu)
      }
    } GroupBy(_.cluster) Select { group => new Record {
        val cluster = group._1
        val avg1 = group._2.Average(l => if (l.classification == 0) 1.0 else 0.0)
        val avg2 = group._2.Average(l => if (l.classification == 1) 1.0 else 0.0)
        val avg3 = group._2.Average(l => if (l.classification == 2) 1.0 else 0.0)
        val avg4 = group._2.Average(l => if (l.classification == 3) 1.0 else 0.0)
      }
    }

    test.printAsTable()

  }
}
