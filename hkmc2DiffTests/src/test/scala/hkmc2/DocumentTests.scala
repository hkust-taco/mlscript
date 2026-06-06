package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time.*
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}

import hkmc2.utils.*, shorthands.*
import document.*
import document.Document.*
import sourcecode.{Line, File}


class DocumentTests extends funsuite.AnyFunSuite:
  
  def runTest(nme: Str)(body: StringBuilder => Unit) =
    test(nme):
      val path = os.pwd/"hkmc2DiffTests"/"src"/"test"/"out"/(nme + ".out")
      
      val contents = if os.exists(path)
        then os.read(path)
        else ""
      
      val strb = new StringBuilder
      
      body(strb)
      
      val res = strb.toString
      if res =/= contents then
        os.write.over(path, res)
        println(s"Updating $path")
      
  
  runTest("Basic Document Tests"): strb =>
    
    strb ++= s"// Generated from: ${os.Path(summon[File].value).relativeTo(os.pwd)}\n"
    
    def mk(d: Document, showRaw: Bool = false)(using Line) =
      strb ++= "\n"
      strb ++= s"// L.${summon[Line].value}:\n"
      if showRaw then strb ++= s"//\t$d\n"
      strb ++= d.mkString(20)
      strb ++= "\n"
    
    mk(doc"hello" :: " " :: doc"world", showRaw = true)
    
    mk(nest(doc"hello" :/: doc"world"), showRaw = true)
    
    mk(doc"hello hello hello" :: break :: doc"world world world")
    
    mk(doc"hello" :: forceBreak :: doc"world")
    
    mk(nest(doc"hello" :: forceBreak :: doc"world"))
    
    mk(nest(doc"hello hello hello" :: break :: doc"world world world"))
    
    mk(group(doc"hello hello hello" :: break :: doc"world world world"))
    
    mk(nest(group(doc"hello hello hello" :: break :: doc"world world world")))
    
    mk(doc"\{hi # hi\} # \{world # world\}")
    
    mk(doc"\{hi # hi\}\n\{world # world\}")
    
    mk(doc"\{hi # hi\} # \{W # W\} # \{! # !\}")
    
    mk(doc"\{hi # hi\}\n\{W # W\} # \{! # !\}")
    
    mk(doc"\{hi # hi\} # \{W # W\}\n\{! # !\}")
    
    mk(doc"\{hi # hi\} # \{world\nworld\}")
    
    mk(doc"\{hello # hello # hello\} # \{world # world # world\}")
    
    mk(doc"\{hello # hello # hello\} # \{universe # universe # universe\}")
    
    mk(doc" #{ \{hello # hello # hello\}\n\{world # world # world\} #} ")
    
    mk(doc" #{ \{hello # hello\nhello\}\n\{world # world # world\} #} ")
    
    mk(doc" #{ \{hello # hello\nhello\}\n\{world # world\nworld\} #} ")
    
    
  
end DocumentTests

