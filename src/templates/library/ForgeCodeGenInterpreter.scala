package ppl.dsl.forge
package templates
package library

import java.io.{File,PrintWriter,FileWriter}
import scala.tools.nsc.io.{Directory,Path}
import scala.reflect.SourceContext
import scala.virtualization.lms.common._
import scala.virtualization.lms.internal.{GenericFatCodegen, GenericCodegen}

import core._
import shared._

trait ForgeCodeGenInterpreter extends ForgeCodeGenBackend with LibGenPackages with BaseGenOps with LibGenImports with LibGenOps {
  val IR: ForgeApplicationRunner with ForgeExp
  import IR._

  lazy val targetName = "library"

  /**
   * Emit the entire library backend
   */
  def emitDSLImplementation() {
    println("[Forge] Emitting library backend")
    Directory(Path(dslDir)).createDirectory()
    emitDSLDefinition()
    emitClasses()
  }

  /**
   * Emit header files which mix in all library ops and which the user can extend
   */
  def emitDSLDefinition() {
    val dslStream = new PrintWriter(new FileWriter(dslDir+dsl+".scala"))
    dslStream.println("package " + packageName)
    dslStream.println()
    emitAllImports(dslStream)
    dslStream.println()
    emitApplicationRunner(OpsGrp.values.toList, dslStream)
    dslStream.println()
    emitDSLPackageDefinitions(OpsGrp.values.toList, dslStream)
    dslStream.println()
    dslStream.close()
  }

  /**
   * Emit the library version of all data structures in the DSL.
   * DSLClasses extends [Grp]Wrapper with [Grp]WrapperImpl with [TpeClassGrp]Ops
   */
  def emitClasses() {
    val clsDir = dslDir + File.separator + "classes"
    Directory(Path(clsDir)).createDirectory()

    // trait to group all of the ops together
    val grpStream = new PrintWriter(new FileWriter(clsDir+File.separator+dsl+"Classes.scala"))
    grpStream.println("package " + packageName + ".classes")
    grpStream.println()
    emitScalaReflectImports(grpStream)
    emitLMSImports(grpStream)
    emitDSLImports(grpStream)
    grpStream.println()
    grpStream.print("trait " + dsl + "Classes extends ")
    var first = true
    for ((grp,opsGrp) <- OpsGrp) {
      if (isTpeClass(grp)) {
        if (first) grpStream.print(opsGrp.name) else grpStream.print(" with " + opsGrp.name)
        first = false
      }
      else if (!isTpeClass(grp) && !isTpeClassInst(grp)) {
        val wrapper = grp.name + "Wrapper"
        if (first) grpStream.print(wrapper) else grpStream.print(" with " + wrapper)
        first = false

        val stream = new PrintWriter(new FileWriter(clsDir+File.separator+grp.name+".scala"))
        stream.println("package " + packageName + ".classes")
        stream.println()
        emitScalaReflectImports(stream)
        emitScalaMathImports(stream)
        emitLMSImports(stream)
        emitDSLImports(stream)
        stream.println()
        stream.println("trait " + wrapper + " {")
        // stream.println("trait " + wrapper + " extends " + grp.name + "Ops with " + dsl + "Base {")
        // Note that Wrapper must not have a view of lifts, as this causes ambiguous implicit calls
        // for the library class implementations (specifically the var fields)
        stream.println( "  this: " + dsl + "Base with " + dsl + "Classes => ")
        stream.println()
        emitClass(opsGrp, stream)
        stream.println("}")
        stream.println()
        stream.close()

        // because front-end types are not in scope (to prevent unintentional recursive calls and ambiguities),
        // we need to factor almost all tasks out to a separate trait in the library version also
        if (opsGrp.ops.exists(requiresImpl)) {
          val implStream = new PrintWriter(new FileWriter(clsDir+File.separator+grp.name+"WrapperImpl"+".scala"))
          implStream.println("package " + packageName + ".classes")
          implStream.println()
          emitScalaReflectImports(implStream)
          emitScalaMathImports(implStream)
          emitDSLImports(implStream)
          implStream.println()
          emitImpls(opsGrp, implStream)
          implStream.close()

          grpStream.print(" with " + grp.name + "WrapperImpl")
        }
      }
    }
    for (d <- DataStructs.keys.toSeq diff OpsGrp.values.flatMap(_.ops).map(_.grp).filter(grpIsTpe).map(grpAsTpe).toSeq if !isMetaType(d)) {
      warn("(library) ignoring data definition for " + d.name + " since it cannot be instantiated in app code (it has no accompanying ops)")
    }
    for (e <- Externs) {
      grpStream.print(" with " + e.opsGrp.grp.name + "Wrapper")
    }
    grpStream.println("{")
    grpStream.println("  this: " + dsl + "Library => ")
    grpStream.println("}")
    grpStream.println()
    grpStream.close()
  }
}

