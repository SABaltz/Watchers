import React from "react";
import {BrowserRouter, Routes} from "react-router-dom";
import NavBar from "./components/NavBar";
import Footer from "./components/Footer";
import Box from "@mui/material/Box";

function App() {
    return (
        <>
            <NavBar/>
            <Box sx={{height: '3000px', backgroundColor:'red'}}></Box>
            <BrowserRouter>
                <Routes>
                    {/*<Route exact path="/" element={<RecordList />} />*/}
                    {/*<Route path="/edit/:id" element={<Edit />} />*/}
                    {/*<Route path="/create" element={<Create />} />*/}
                </Routes>
            </BrowserRouter>
            <Footer/>
        </>
    );
}

export default App;
