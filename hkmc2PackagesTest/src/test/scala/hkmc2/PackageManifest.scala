package hkmc2

import hkmc2.utils.*, shorthands.*

case class PackageManifest(
  name: Str,
  main: Str,
  moduleName: Str,
  vendors: Ls[VendorManifest],
)

/** Represents an entry in the `vendors` field of the manifest. */
case class VendorManifest(prefix: Str, path: Str, files: Ls[Str])

object PackageManifest:
  
  /** Parse a package's manifest.json file. */
  def read(packageDir: os.Path): PackageManifest =
    val manifestPath = packageDir / "manifest.json"
    val json = ujson.read(os.read(manifestPath))
    val obj = json match
      case ujson.Obj(value) => value
      case _ => throw new Exception(s"Expected JSON object in $manifestPath")
    PackageManifest(
      stringField(obj, "name", manifestPath),
      stringField(obj, "main", manifestPath),
      stringField(obj, "moduleName", manifestPath),
      vendors(obj, manifestPath),
    )
  
  /** Parse a required string field. */
  private def stringField(obj: collection.Map[Str, ujson.Value], name: Str, manifestPath: os.Path): Str =
    obj.get(name) match
      case S(ujson.Str(value)) => value
      case S(_) => throw new Exception(s"Expected string field '$name' in $manifestPath")
      case N => throw new Exception(s"Missing string field '$name' in $manifestPath")
  
  /** Parse the optional vendors array. */
  private def vendors(obj: collection.Map[Str, ujson.Value], manifestPath: os.Path): Ls[VendorManifest] =
    obj.get("vendors") match
      case S(ujson.Arr(values)) =>
        values.toList.map:
          case ujson.Obj(vendor) =>
            VendorManifest(
              stringField(vendor, "prefix", manifestPath),
              stringField(vendor, "path", manifestPath),
              stringArrayField(vendor, "files", manifestPath),
            )
          case _ => throw new Exception(s"Expected object entries in 'vendors' in $manifestPath")
      case S(_) => throw new Exception(s"Expected array field 'vendors' in $manifestPath")
      case N => Nil
  
  /** Parse a required string array field. */
  private def stringArrayField(obj: collection.Map[Str, ujson.Value], name: Str, manifestPath: os.Path): Ls[Str] =
    obj.get(name) match
      case S(ujson.Arr(values)) =>
        values.toList.map:
          case ujson.Str(value) => value
          case _ => throw new Exception(s"Expected string entries in '$name' in $manifestPath")
      case S(_) => throw new Exception(s"Expected string array field '$name' in $manifestPath")
      case N => throw new Exception(s"Missing string array field '$name' in $manifestPath")
