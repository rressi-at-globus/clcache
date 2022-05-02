from conans import ConanFile

class ClcacheConan(ConanFile):
    name = "clcache"
    version = "4.2.13"
    author = "Daniel Gehriger <dgehriger@globusmedical.com>"
    settings = "os", "arch"
    description = "A compiler cache for Microsoft Visual Studio"
    url = "https://github.com/rressi-at-globus/clcache"
    license = "https://github.com/rressi-at-globus/clcache/blob/master/LICENSE"
    user = "rressi-at-globus"
    channel = "stable"

    def package(self):
        self.copy("*", dst="bin", src="../clcache.dist")
        self.copy("*", dst=".", src="doc")

    def package_info(self):
        self.cpp_info.libs = []

    def configure(self):
        if self.settings.os != "Windows" or self.settings.arch != "x86_64":
            raise Exception("This package does not support this configuration")