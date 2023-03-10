object Main {
  def main(args: Array[String]): Unit = DriverOptions.parse match {
    case Some(options) => {
      val driver = Driver(options)
      driver.execute
      driver.flush()
    }
    case _ => System.out.println("Usage: mlsc filename.mls [outputDir]")
  }
}
