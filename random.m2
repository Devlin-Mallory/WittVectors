---Installing package from scratch

uninstallPackage "WittVectors"
restart
path = append(path, "~/GitHub/WittVectors")
installPackage ("WittVectors", FileName => "~/GitHub/WittVectors/WittVectors.m2")
