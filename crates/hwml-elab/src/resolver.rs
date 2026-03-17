use hwml_core::*;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Resolver<'db> {
    package: Option<QualifiedName<'db>>,
}

impl<'db> Resolver<'db> {
    pub fn new(package: Option<QualifiedName<'db>>) -> Self {
        Resolver { package }
    }

    pub fn package(&self) -> Option<QualifiedName<'db>> {
        self.package
    }

    pub fn qualify<Db>(&self, db: &'db Db, name: Name<'db>) -> QualifiedName<'db>
    where
        Db: salsa::Database,
    {
        QualifiedName::new(db, self.package, name)
    }

    pub fn resolve<Db>(
        &self,
        db: &'db Db,
        name: Name<'db>,
        global_env: &GlobalEnv<'db>,
    ) -> Option<QualifiedName<'db>>
    where
        Db: salsa::Database + ?Sized,
    {
        let mut package = self.package;
        while let Some(pkg) = package {
            let qualified = QualifiedName::new(db, Some(pkg), name);
            if global_env.contains(qualified) {
                return Some(qualified);
            }
            package = pkg.package(db);
        }

        let qualified = QualifiedName::new(db, None, name);
        if global_env.contains(qualified) {
            Some(qualified)
        } else {
            None
        }
    }
}
