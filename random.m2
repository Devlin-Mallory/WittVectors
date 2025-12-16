---Installing package from scratch

uninstallPackage "WittVectors"
restart
path = append(path, "~/GitHub/WittVectors")
installPackage ("WittVectors", FileName => "~/GitHub/WittVectors/WittVectors.m2")

---Empty doc
doc ///
    Key

    Headline
	
	
    Usage
	
    Inputs
	
    Outputs
	
    Description
	Text
	    
	Example
	
    SeeAlso
	    
///
