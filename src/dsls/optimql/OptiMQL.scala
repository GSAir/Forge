package ppl.dsl.forge
package dsls
package optimql

import optiml.{OptiMLDSL}

import core.{ForgeApplication,ForgeApplicationRunner}

object OptiMQLDSLRunner extends ForgeApplicationRunner with OptiMQLDSL

trait OptiMQLDSL extends OptiMLDSL with TableMQLOps {
  /**
   * The name of your DSL. This is the name that will be used in generated files,
   * package declarations, etc.
   */
  override def dslName = "OptiMQL"

  override def addREPLOverride = false

  /**
   * The specification is the DSL definition (types, data structures, ops)
   */
  override def specification() = {
    // our selection of Scala ops
    // we don't use Numeric or Fractional, since they are replaced by Arith
    importPrimitives()
    importMisc()
    importCasts()
    importOrdering()
    importStrings()
    importMath()
    importTuples()
    importHashMap()
    importConcurrentHashMap()

    extern(grp("Rewrite"))
    importTableOps()
    extern(grp("Date"))

    // OptiLA types
    // declare all tpes first, so that they are available to all ops (similar to Delite)
    val T = tpePar("T")
    val DenseVector = tpe("DenseVector", T)
    val DenseVectorView = tpe("DenseVectorView", T)
    val DenseMatrix = tpe("DenseMatrix", T)
    val DenseMatrixView = tpe("DenseMatrixView", T)
    val IndexVector = tpe("IndexVector")
    val IndexWildcard = tpe("IndexWildcard", stage = compile)
    identifier (IndexWildcard) ("*")
    val SparseVector = tpe("SparseVector", T)
    val SparseVectorView = tpe("SparseVectorView", T)
    val SparseMatrix = tpe("SparseMatrix", T)
    val SparseMatrixBuildable = tpe("SparseMatrixBuildable", T)

    // OptiLA ops
    // note that the order matters with respect to 'lookup' calls

    // sneak in a compiler-only range method
    val Range = tpe("Range")
    data(Range, ("start", MInt), ("end", MInt))
    compiler (Range) ("range_start", Nil, Range :: MInt) implements getter(0, "start")
    compiler (Range) ("range_end", Nil, Range :: MInt) implements getter(0, "end")

    noInfixList :::= List("infix_foreach")
    compiler (Range) ("infix_until", Nil, (MInt,MInt) :: Range) implements allocates(Range, quotedArg(0), quotedArg(1))

    // infix_foreach must be compiler only both so that it is not used improperly and to not interfere with other codegen nodes in the library
    // this is a little convoluted unfortunately (because of the restriction on passing structs to codegen nodes)
    compiler (Range) ("infix_foreach", Nil, (Range, MInt ==> MUnit) :: MUnit) implements composite ${ range_foreach(range_start($0), range_end($0), $1) }
    val range_foreach = compiler (Range) ("range_foreach", Nil, (("start",MInt),("end",MInt),("func",MInt ==> MUnit)) :: MUnit)
    impl (range_foreach) (codegen($cala, ${
      var i = $start
      while (i < $end) {
        $b[func](i)
        i += 1
      }
    }))

    impl (range_foreach) (codegen(cpp, ${
      for(int i=$start ; i<$end ; i++) {
        $b[func](i)
      }
    }))

    importArithOps()
    importBasicMathOps()
    importRandomOps()
    importHasMinMaxOps()
    importStringableOps()
    importComplexOps()

    // override default string formatting (numericPrecision is a global defined in extern)
    // we use "" + $a instead of $a.toString to avoid an NPE when explicitly calling toString inside the REPL
    val formatStr = {
      val a = quotedArg(0)
      val f = "(\"% .\"+Global.numericPrecision+\"g\")" // can't escape quotes inside string interpolation scope

s"""
def numericStr[A](x: A) = {
  val s = $f.format(x)
  val padPrefix = (Global.numericPrecision+6) - s.length
  if (padPrefix > 0) " "*padPrefix + s else s
}
if ($a.isInstanceOf[Double] || $a.isInstanceOf[Float]) numericStr($a) else ("" + $a)
"""
    }

    val fmt_str = direct (lookupGrp("FString")) ("optila_fmt_str", T, T :: MString)
    impl (fmt_str) (codegen($cala, formatStr))
    impl (fmt_str) (codegen(cpp, "convert_to_string<" +  unquotes("remapWithRef("+opArgPrefix+"0.tp)") + " >(" + quotedArg(0) + ")"))

    compiler (lookupGrp("FString")) ("optila_padspace", Nil, MString :: MString) implements composite ${
      "  " + $0
      // if ($0.startsWith("-")) "  " + $0 else "   " + $0
    }

    importIndexVectorOps()
    importDenseVectorViewOps()
    importDenseVectorOps()
    importDenseMatrixOps()
    importDenseMatrixViewOps()
    importSparseVectorOps()
    importSparseVectorViewOps()
    importSparseMatrixOps()
    importVecMatConstructor()
    importIOOps()
    importLinAlgOps()
    importShapeOps()

    // OptiML types
    val V = tpePar("V")
    // val W = tpePar("W")
    val HashStream = tpe("HashStream", V)
    val FileStream = tpe("FileStream")
    val ComputeStream = tpe("ComputeStream", T)

    // OptiML ops
    importSetOps()
    importTrainingSetLikeOps()
    importByteBuffer()
    extern(grp("Sum"))
    importBufferableOps()
    // importFeatureOps()
    // importFeatureHelperOps()
    importUntilConverged()
    // importAllGraphOps()
    // importAllFactorGraphOps()
    // importMLIOOps()
    // importStreamOps()
    // importImageOps()
    importTreeOps()
    importClassifierOps()
    importValidateOps()
  }
}
