object Main {
  def main(args: Array[String]): Unit = DriverOptions.parse match {
    case Some(options) => Driver(options).execute
    case _ => System.out.println("Usage: mlsc filename.mls [outputDir]")
  }
}
