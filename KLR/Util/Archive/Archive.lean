/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amazon Q
-/

namespace Util

/-- A structure representing a file entry in an archive -/
structure ArchiveEntry where
  /-- The filename (path) of the entry -/
  filename : String
  /-- The content of the file as a ByteArray -/
  content : ByteArray
  deriving Inhabited

/-- Create a tar archive from a list of file entries -/
@[extern "lean_archive_create_tar"]
opaque createTar (entries : @&List ArchiveEntry) : ByteArray

/-- Extract files from a tar archive -/
@[extern "lean_archive_extract_tar"]
opaque extractTar (bytes : @&ByteArray) : List ArchiveEntry

end Util
